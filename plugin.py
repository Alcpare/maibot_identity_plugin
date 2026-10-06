"""身份认知插件

手动白名单（QQ → 档位）→ 在她「决定要不要回」和「写回复」之前，
注入一条不含任何号码的说明，让她知道当前对话者是谁、该怎么对待。

设计要点
--------
1. QQ 号只活在本插件的内存表里（msg_id → user_id），**永不进入提示词**；
   渲染后的注入文本还会过一遍长数字自检，命中就拒绝注入（硬保证）。
2. 当前说话者按消息 ID 精确定位，不靠名字匹配 —— 同名、改名都不怕。
   宿主的消息 ID 有两种出现形式，都要认：
   - planner 上下文：``<message msg_id="123456" time="10:00" user="某某">``
   - replyer / 记忆侧可见文本：``[10:00:00][msg_id:123456][某某]内容``
   超长 ID 会被宿主缩短为 ``m`` + 6 位别名，所以映射表同时按原 ID 与别名建索引。
3. 名单里只写 ``QQ = 档位``；显示名实时取消息里的群名片/昵称，
   所以改群名片、改昵称都不用维护名单。
4. 名单为空、或当前说话者不在名单里 → 完全不注入（等于没装插件）。
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import time
import unicodedata
import uuid
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from maibot_sdk import Field, HookHandler, MaiBotPlugin, PluginConfigBase
from maibot_sdk.types import ErrorPolicy, HookMode, HookOrder

# ── 常量 ──────────────────────────────────────────────────────────────

_ITEM_SYSTEM = "SystemMessageItem"
"""Context Items 里 system 消息条目的 item_type（与复读机插件保持一致）。"""

_MSG_ID_RE = re.compile(r"\[msg_id:([^\]]+)\]")
"""replyer / 记忆侧的消息 ID 前缀，形如 ``[msg_id:123456]``。"""

_PLANNER_MSG_ID_RE = re.compile(r'msg_id="([^"]+)"')
"""planner 上下文的消息 ID 属性，形如 ``<message msg_id="123456" time="10:00" user="某某">``。"""

_MAX_PLAIN_ID_LEN = 12
"""宿主阈值：不超过该长度的消息 ID 原样展示，超出则缩短为别名。"""

_ALIAS_PREFIX = "m"
_ALIAS_HASH_LENGTH = 6

_LONG_DIGITS_RE = re.compile(r"\d{5,}")
"""长数字自检：注入文本中出现 5 位以上连续数字就拒绝注入。"""

_DEFAULT_LABEL = "群友"

_NOTE_MARKER = "【内部参考"
"""注入文本的固定抬头；用它判断同一轮是否已经注入过（自去重）。"""

_NAME_MAX_LEN = 24
"""显示名长度上限（防止超长群名片把注入文本撑爆）。"""

_NAME_DROP_CATEGORIES = frozenset(
    {
        "Cc",  # 控制字符（换行/制表等）
        "Cf",  # 格式字符（零宽/RTL 覆盖等）
        "Ps", "Pe",  # 任何文字的开/闭括号（半角、全角、书名号、方括号…）
        "Pi", "Pf",  # 各类弯引号
        "Sm", "Sk", "Sc",  # 数学/修饰/货币符号（| ~ ^ = $ 等）
        "Pc",  # 连接符（下划线等）
    }
)
_NAME_DROP_CHARS = frozenset("'\"*")
"""额外剔除的直引号与星号（它们的 Unicode 类别是普通标点，需单独列）。

现实威胁：群名片是**用户可控**的，恶意群友可以把它写成指令文本，
跟着我们的系统项一起进入模型上下文（「5 位以上数字」自检拦不住这种）。
括号类字符必须**全部**剔除 —— 枚举式黑名单一定会漏（实测就漏了全角 `（）`），
所以这里按 Unicode 类别过滤：任何文字的括号、引号、符号都进不来。
再叠加长度上限，把注入面压到最小。
"""

_INJECT_DEDUPE_TTL = 900.0
"""同轮去重记录的保留时长（秒）。"""

_LABEL_RULES: Dict[str, str] = {
    "主人": (
        "最亲近的人。可以放松、撒娇、更坦白；他开玩笑可以顺着接，不用客套。"
        "关心要自然、点到为止：一段对话里提一两次就够，他不听就随他去，别反复念同一件事。"
    ),
    "朋友": (
        "熟人。语气自然，能闲聊打趣、能吐槽；不必客气，但也不过分亲昵。"
        "关心最多温和提一句，不劝、不催。"
    ),
    "群友": (
        "普通群成员。礼貌、简短、有分寸；不主动贴上去，不打听私事，冷场就安静待着，"
        "也不要劝对方做这做那。"
    ),
}

_RECENT_LIMIT = 2000
"""msg_id → 说话者 的内存映射上限，超出后按时间淘汰。"""

_RECENT_TTL = 6 * 3600.0
"""映射保留时长（秒）。放宽到 6 小时：消息可能被频率调度延迟很久才进 planner。"""

_PERSIST_LIMIT = 800
"""落盘保留的映射条数（取最近的部分，足够覆盖延迟消息）。"""

_PERSIST_SESSION_LIMIT = 200
"""落盘保留的会话兜底条数。"""

_FULLWIDTH_MAP = str.maketrans({"＝": "=", "，": ",", "；": ";", "：": ":", "　": " "})
"""中文输入法常打出全角标点，解析名单前统一转半角。"""


# ── 配置模型 ──────────────────────────────────────────────────────────


class PluginSectionConfig(PluginConfigBase):
    """插件基础配置。"""

    __ui_label__ = "插件"
    __ui_icon__ = "package"
    __ui_order__ = 0

    enabled: bool = Field(default=True, description="是否启用插件")
    config_version: str = Field(default="1.0.0", description="配置版本")


class IdentitySectionConfig(PluginConfigBase):
    """身份名单与三档语气。"""

    __ui_label__ = "身份名单"
    __ui_icon__ = "users"
    __ui_order__ = 1

    # ── 1. 名单（必填项，其余都可以不动）────────────────────────────
    roster: str = Field(
        default=(
            "# 每行一位，格式：QQ号 = 档位\n"
            "# 档位可填：主人 / 朋友（没列出来的人按「群友」对待）\n"
            "# 不用写名字：她的显示名实时取自群名片/昵称，改名也不影响。\n"
            "# QQ 号只用于内部识别，永远不会进入她的提示词。\n"
            "# 示例：\n"
            "# 100000001 = 主人\n"
            "# 100000002 = 朋友\n"
        ),
        description="白名单：每行「QQ号 = 档位（主人/朋友）」，# 开头为注释；保存即生效",
    )

    # ── 2. 三档的态度与关心程度（想调她的分寸就改这里）────────────
    owner_style: str = Field(
        default=_LABEL_RULES["主人"],
        description="「主人」档：语气 + 关心到什么程度（写得越具体她越照做，但别举具体行为的例子）",
    )
    friend_style: str = Field(
        default=_LABEL_RULES["朋友"],
        description="「朋友」档：语气 + 关心程度",
    )
    member_style: str = Field(
        default=_LABEL_RULES["群友"],
        description="「群友」档：名单内外、以及没列出来的人默认按这一档",
    )
    default_label: str = Field(
        default=_DEFAULT_LABEL,
        description="名单外的人按哪一档对待（一般保持「群友」）",
    )

    # ── 3. 开关（默认值就是推荐值，通常不用动）─────────────────────
    inject_to_planner: bool = Field(default=True, description="在她决定要不要回之前注入（建议开）")
    inject_to_replyer: bool = Field(default=True, description="在她写回复之前注入（建议开）")
    inject_for_others: bool = Field(
        default=False,
        description="名单【外】的人也注入：关=只对名单内生效（省 token，推荐）；开=对所有人注入",
    )
    log_injections: bool = Field(default=True, description="把每次注入记入日志（便于核对效果）")


class IdentityPluginConfig(PluginConfigBase):
    """身份认知插件配置。"""

    plugin: PluginSectionConfig = Field(default_factory=PluginSectionConfig)
    identity: IdentitySectionConfig = Field(default_factory=IdentitySectionConfig)


# ── 插件主体 ──────────────────────────────────────────────────────────


class IdentityPlugin(MaiBotPlugin):
    """手动白名单驱动的身份认知插件。"""

    config_model = IdentityPluginConfig

    def __init__(self) -> None:
        super().__init__()
        self._recent: Dict[str, Dict[str, Any]] = {}
        self._latest_by_session: Dict[str, Dict[str, Any]] = {}
        self._labels: Dict[str, str] = {}
        self._injected_keys: Dict[str, float] = {}
        self._warned_no_target = False
        self._last_save = 0.0
        self._data_file = None

    # ── 生命周期 ──────────────────────────────────────────────────────

    async def on_load(self) -> None:
        """解析名单 + 恢复上次运行留下的说话者映射。"""

        self._rebuild_roster()
        self._load_persisted()
        data_file = self._resolve_data_file()
        try:
            file_note = (
                f"{data_file}（{data_file.stat().st_size} B）"
                if data_file and data_file.exists()
                else f"{data_file}（不存在）"
            )
        except Exception:  # noqa: BLE001
            file_note = str(data_file)
        self.ctx.logger.info(f"[身份] 映射文件: {file_note}")
        self.ctx.logger.info(
            f"[身份] 已加载：名单 {len(self._labels)} 人（"
            + "、".join(f"{self._mask_id(qq)}→{lab}" for qq, lab in list(self._labels.items())[:5])
            + ("…" if len(self._labels) > 5 else "")
            + "）；"
            f"注入了阶段={'planner+replyer' if self.config.identity.inject_to_planner and self.config.identity.inject_to_replyer else ('planner' if self.config.identity.inject_to_planner else ('replyer' if self.config.identity.inject_to_replyer else '无'))}；"
            f"名单外={'注入' if self.config.identity.inject_for_others else '不注入'}；"
            f"恢复映射 {len(self._recent)} 条（会话 {len(self._latest_by_session)} 个）"
        )

    async def on_unload(self) -> None:
        """落盘并清理内存映射。"""

        self._save_persisted(force=True)
        self._recent.clear()
        self._latest_by_session.clear()
        self._labels.clear()

    async def on_config_update(self, scope: str, config_data: dict[str, object], version: str) -> None:
        """配置热重载：重新解析名单，改动立即生效。"""

        del scope, config_data, version
        self._rebuild_roster()
        self.ctx.logger.info(f"[身份] 名单已刷新：{len(self._labels)} 人")

    # ── 名单解析 ──────────────────────────────────────────────────────

    def _rebuild_roster(self) -> None:
        """把多行文本名单解析成 {QQ: 档位}；容忍空格、中文标点与注释。"""

        labels: Dict[str, str] = {}
        raw = str(self.config.identity.roster or "").translate(_FULLWIDTH_MAP)
        for line in raw.splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            body = line.split("#", 1)[0].strip()
            if "=" in body:
                left, right = body.split("=", 1)
            elif "," in body:
                left, right = body.split(",", 1)
            else:
                continue
            qq = re.sub(r"\D", "", left)
            label = right.strip().split()[0] if right.strip() else ""
            if label not in _LABEL_RULES:
                self.ctx.logger.warning(f"[身份] 名单第「{line}」行档位无法识别，已跳过")
                continue
            if qq:
                labels[qq] = label
        self._labels = labels

    def _label_for(self, user_id: str) -> Tuple[str, bool]:
        """返回 (档位, 是否命中名单)。"""

        label = self._labels.get(str(user_id))
        if label:
            return label, True
        return str(self.config.identity.default_label or _DEFAULT_LABEL), False

    def _style_for(self, label: str) -> str:
        """按档位取「态度 + 关心程度」文案（来自配置，可在面板里改）。"""

        cfg = self.config.identity
        table = {
            "主人": cfg.owner_style,
            "朋友": cfg.friend_style,
            "群友": cfg.member_style,
        }
        text = str(table.get(label) or "").strip()
        return text or _LABEL_RULES.get(label, _LABEL_RULES[_DEFAULT_LABEL])

    # ── 隐私与注入面处理 ──────────────────────────────────────────────

    @staticmethod
    def _mask_id(value: Any) -> str:
        """日志用：把 QQ 号/会话 ID 遮蔽成 ``123***890``。

        日志一旦被贴出来就等于公开了身份名单，所以号码不进日志。
        """

        text = str(value or "").strip()
        if not text:
            return "-"
        if len(text) <= 4:
            return "*" * len(text)
        if len(text) <= 8:
            return f"{text[:2]}***"
        return f"{text[:3]}***{text[-3:]}"

    @staticmethod
    def _sanitize_name(value: Any) -> str:
        """规范化显示名：按 Unicode 类别剔除括号/引号/符号与控制字符 → 截断 → 兜底「某人」。"""

        text = "".join(
            ch
            for ch in str(value or "")
            if ch not in _NAME_DROP_CHARS and unicodedata.category(ch) not in _NAME_DROP_CATEGORIES
        )
        text = re.sub(r"\s{2,}", " ", text).strip()
        if len(text) > _NAME_MAX_LEN:
            text = text[:_NAME_MAX_LEN] + "…"
        return text or "某人"

    # ── 入口：记住每条消息的说话者（QQ 只活在这里）────────────────────

    @HookHandler(
        "chat.receive.before_process",
        name="identity_remember_speaker",
        description="记录 msg_id → 说话者(QQ/显示名/会话)，供后续精确定位；不拦截消息",
        mode=HookMode.BLOCKING,
        order=HookOrder.EARLY,
        timeout_ms=3000,
        error_policy=ErrorPolicy.SKIP,
    )
    async def remember_speaker(self, message: dict | None = None, **kwargs: Any) -> Optional[dict]:
        """把入站消息的说话者记进内存映射，然后放行。

        这里必须永不抛异常：本钩子只是"记账"，任何失败都不该影响消息处理。
        所以整体包了 try/except，并把失败写进 WARNING 日志（否则会被 ErrorPolicy.SKIP
        静默吞掉，只能去控制台才看得到）。
        """

        del kwargs
        if not self.config.plugin.enabled or not isinstance(message, dict):
            return None

        try:
            message_id = str(message.get("message_id") or "").strip()
            info = message.get("message_info") or {}
            user_info = info.get("user_info") or {}
            group_info = info.get("group_info") or {}
            user_id = str(user_info.get("user_id") or "").strip()
            if not message_id or not user_id:
                return None

            display_name = self._sanitize_name(
                user_info.get("user_cardname") or user_info.get("user_nickname") or ""
            )
            session_id = str(message.get("session_id") or "")
            is_notify = bool(message.get("is_notify"))

            record = {
                "user_id": user_id,
                "name": display_name,
                "session": session_id,
                "group": str(group_info.get("group_id") or ""),
                "ts": time.time(),
                "is_notify": is_notify,
            }

            if is_notify or message_id.startswith("qq-notice"):
                # 通知类事件（入群/退群/撤回/戳一戳等）不是"有人在说话"：
                # 它的发送者往往是操作者（比如"你邀请 awa 加入了群聊"的发送者是你），
                # 若当成消息记账，就会让下一轮误判"本条消息来自 XXX"。
                # 只在会话最新事件里留个标记，供注入前判断"最新事件是不是通知"。
                if session_id:
                    self._latest_by_session[session_id] = record
                self.ctx.logger.debug(
                    f"[身份] 入口忽略通知事件: msg_id={message_id} "
                    f"发送者={self._mask_id(user_id)} session={self._mask_id(session_id)}"
                )
                return None

            # 索引 1：原始消息 ID + 宿主可能使用的短别名（超长 ID 会被宿主缩短）
            self._recent[message_id] = record
            alias = self._display_message_id(message_id)
            if alias and alias != message_id:
                self._recent.setdefault(alias, record)
            # 索引 2：该会话最近一条消息（当上下文里读不到消息 ID 时的兜底）
            if session_id:
                self._latest_by_session[session_id] = record

            self._prune_recent()
            self._save_persisted()  # 节流落盘：重启/重载后延迟消息仍能定位
            self.ctx.logger.debug(
                f"[身份] 入口记录: msg_id={message_id}(alias={alias}) "
                f"user_id={self._mask_id(user_id)} "
                f"session={self._mask_id(session_id)} "
                f"group={self._mask_id(group_info.get('group_id')) if group_info.get('group_id') else '(私聊)'}"
            )
        except Exception as exc:  # noqa: BLE001 - 记账失败绝不能影响消息处理
            self.ctx.logger.warning(f"[身份] 入口记录失败（已忽略，不影响收发）: {type(exc).__name__}: {exc}")
        return None  # 不拦截、不改写

    def _prune_recent(self) -> None:
        """按 TTL + 上限清理映射，避免长期运行内存增长。"""

        now = time.time()
        stale = [k for k, v in self._recent.items() if now - float(v.get("ts") or 0) > _RECENT_TTL]
        for key in stale:
            self._recent.pop(key, None)
        if len(self._recent) > _RECENT_LIMIT:
            ordered = sorted(self._recent.items(), key=lambda kv: float(kv[1].get("ts") or 0))
            for key, _ in ordered[: len(self._recent) - _RECENT_LIMIT]:
                self._recent.pop(key, None)
        for session_id, record in list(self._latest_by_session.items()):
            if now - float(record.get("ts") or 0) > _RECENT_TTL:
                self._latest_by_session.pop(session_id, None)

    # ── 映射持久化：重启/重载后仍能定位延迟处理的消息 ────────────────

    def _resolve_data_file(self) -> Optional[Path]:
        """返回插件数据目录下的映射文件路径（拿不到就返回 None）。"""

        if self._data_file is not None:
            return self._data_file
        try:
            data_dir = Path(self.ctx.paths.data_dir)
            data_dir.mkdir(parents=True, exist_ok=True)
            self._data_file = data_dir / "speakers.json"
        except Exception as exc:  # noqa: BLE001
            self.ctx.logger.debug(f"[身份] 无法准备数据目录，映射将不落盘: {exc}")
            self._data_file = False  # type: ignore[assignment]
        return self._data_file or None  # type: ignore[return-value]

    def _load_persisted(self) -> None:
        """启动时恢复映射（按 TTL 过滤，坏了就当没有）。"""

        path = self._resolve_data_file()
        if path is None or not path.exists():
            return
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception as exc:  # noqa: BLE001
            self.ctx.logger.warning(f"[身份] 映射文件损坏，已忽略: {type(exc).__name__}: {exc}")
            return
        now = time.time()
        recent = payload.get("recent") if isinstance(payload, dict) else None
        latest = payload.get("latest") if isinstance(payload, dict) else None
        if isinstance(recent, dict):
            for key, record in recent.items():
                if isinstance(record, dict) and now - float(record.get("ts") or 0) <= _RECENT_TTL:
                    self._recent[str(key)] = record
        if isinstance(latest, dict):
            for key, record in latest.items():
                if isinstance(record, dict) and now - float(record.get("ts") or 0) <= _RECENT_TTL:
                    self._latest_by_session[str(key)] = record

    def _save_persisted(self, force: bool = False) -> None:
        """把映射原子落盘；默认节流（最多每 10 秒一次）。"""

        now = time.time()
        if not force and now - self._last_save < 10.0:
            return
        path = self._resolve_data_file()
        if path is None:
            return
        try:
            recent_items = sorted(self._recent.items(), key=lambda kv: float(kv[1].get("ts") or 0))
            payload = {
                "version": 1,
                "updated": now,
                "recent": dict(recent_items[-_PERSIST_LIMIT:]),
                "latest": dict(list(self._latest_by_session.items())[-_PERSIST_SESSION_LIMIT:]),
            }
            tmp = path.with_suffix(".json.tmp")
            tmp.write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")
            os.replace(tmp, path)
            self._last_save = now
        except Exception as exc:  # noqa: BLE001 - 落盘失败不影响注入
            self.ctx.logger.debug(f"[身份] 映射落盘失败: {type(exc).__name__}: {exc}")

    @staticmethod
    def _display_message_id(message_id: str) -> str:
        """与宿主 ``to_display_message_id`` 保持一致的展示用 ID。

        宿主的规则：不超过 12 个字符原样展示，超出则用 ``m`` + 6 位 base32(sha1) 短别名。
        QQ/NapCat 的数字消息 ID 通常很短，会原样出现；这里兼容两种情况。
        """

        normalized = str(message_id or "").strip()
        if len(normalized) <= _MAX_PLAIN_ID_LEN:
            return normalized
        digest = hashlib.sha1(normalized.encode("utf-8")).digest()
        encoded = base64.b32encode(digest).decode("ascii").lower()
        return _ALIAS_PREFIX + encoded[:_ALIAS_HASH_LENGTH]

    # ── 注入点：planner（决定要不要回）与 replyer（决定怎么说）────────

    @HookHandler(
        "maisaka.planner.before_request",
        name="identity_planner_note",
        description="在她决定要不要回复之前，注入当前对话者的身份认知",
        mode=HookMode.BLOCKING,
        order=HookOrder.NORMAL,
        error_policy=ErrorPolicy.SKIP,
    )
    async def inject_to_planner(self, **kwargs: Any) -> dict:
        """planner 侧注入。"""

        self._diag_dump(kwargs.get("items"))
        return self._handle_injection(kwargs, stage="planner")

    @HookHandler(
        "maisaka.replyer.before_model_request",
        name="identity_replyer_note",
        description="在她生成回复之前，注入当前对话者的身份认知",
        mode=HookMode.BLOCKING,
        order=HookOrder.NORMAL,
        error_policy=ErrorPolicy.SKIP,
    )
    async def inject_to_replyer(self, **kwargs: Any) -> dict:
        """replyer 侧注入。"""

        return self._handle_injection(kwargs, stage="replyer")

    # ── 注入实现 ──────────────────────────────────────────────────────

    def _handle_injection(self, kwargs: dict, stage: str) -> dict:
        """统一处理：判定 → 渲染 → 自检 → 写入。"""

        base = {"action": "continue", "modified_kwargs": kwargs}
        cfg = self.config.identity
        if not self.config.plugin.enabled:
            return base
        if stage == "planner" and not cfg.inject_to_planner:
            return base
        if stage == "replyer" and not cfg.inject_to_replyer:
            return base

        # 本轮若是被"通知事件"触发（入群/退群/撤回/戳一戳…），就没有"当前说话者"可言：
        # 上下文里最后一条真实消息可能已经是一分钟前的事了，硬注入它的身份会把她的注意力
        # 拉回旧话题（实测踩过：入群通知被当成 Alcpare 说话，她回头去答旧问题）。
        latest_event = self._latest_by_session.get(str(kwargs.get("session_id") or "").strip())
        if isinstance(latest_event, dict) and latest_event.get("is_notify"):
            self.ctx.logger.debug(
                f"[身份][跳过/{stage}] 该会话最新事件是通知（不是有人说话），本轮不注入"
            )
            return base

        speaker = self._current_speaker(kwargs.get("items"))
        source = "上下文消息ID"
        turn_key = self._last_message_id(kwargs.get("items"))
        if speaker is None:
            # 兜底：上下文里读不到消息 ID 时，用该会话最近一条消息的说话者
            speaker = self._speaker_by_session(kwargs.get("session_id"))
            source = "会话兜底"
            turn_key = ""
        if speaker is None:
            # 每个"不注入"的出口都要说话，否则出问题只能靠猜
            keys = ",".join(sorted(kwargs.keys())) or "(空)"
            self.ctx.logger.debug(
                f"[身份][跳过/{stage}] 无法定位当前说话者："
                f"items={'有' if isinstance(kwargs.get('items'), list) else '无'} "
                f"会话映射={len(self._latest_by_session)} 条 参数键={keys}"
            )
            return base  # 没有映射就不猜

        # 同一轮只注入一次：先看上下文里是否已有我们的抬头，再按 (阶段/会话/消息ID) 去重
        dedupe_key = self._dedupe_key(stage, kwargs.get("session_id"), turn_key)
        if self._note_already_present(kwargs.get("items")) or self._is_duplicate(dedupe_key):
            self.ctx.logger.debug(f"[身份][跳过/{stage}] 本轮已注入过，跳过（key={dedupe_key}）")
            return base

        label, listed = self._label_for(speaker["user_id"])
        if not listed and not cfg.inject_for_others:
            self.ctx.logger.debug(
                f"[身份][跳过/{stage}] 说话者不在名单（且只对名单内生效）："
                f"user_id={self._mask_id(speaker['user_id'])} 名字={speaker.get('name') or '?'}（来源={source}）"
            )
            return base

        note = self._render_note(speaker, label)
        if not note:
            self.ctx.logger.debug(f"[身份][跳过/{stage}] 渲染结果为空")
            return base

        if _LONG_DIGITS_RE.search(note):
            # 硬保证：号码绝不进入提示词
            self.ctx.logger.warning("[身份] 注入文本含长数字，已拒绝注入（请检查名单/提示词）")
            return base

        target = self._append_note(kwargs, note)
        if target is None:
            if not self._warned_no_target:
                self._warned_no_target = True
                self.ctx.logger.warning(f"[身份] {stage} 钩子既无 items 也无 extra_prompt，本次未注入")
            return base
        self._warned_no_target = False
        self._mark_injected(dedupe_key)

        if cfg.log_injections:
            self.ctx.logger.info(
                f"[身份] 已注入({stage}/{target})：{speaker['name'] or '某人'} → {label}"
                + ("（名单外）" if not listed else "")
            )
        return base

    def _current_speaker(self, items: Any) -> Optional[Dict[str, Any]]:
        """从 Context Items 里找**最后一条**消息的消息 ID，反查说话者。

        兼容两种消息 ID 形式：
        - planner 上下文：``<message msg_id="123456" time="10:00" user="某某">``
        - replyer / 记忆侧：``[10:00:00][msg_id:123456][某某]内容``
        """

        if not isinstance(items, list):
            return None
        for item in reversed(items):
            if not isinstance(item, dict):
                continue
            for part in reversed(item.get("parts") or []):
                if not isinstance(part, dict):
                    continue
                text = part.get("text")
                if not isinstance(text, str):
                    continue
                found = _PLANNER_MSG_ID_RE.findall(text) + _MSG_ID_RE.findall(text)
                for message_id in reversed(found):
                    record = self._recent.get(str(message_id).strip())
                    if record:
                        return record
        return None

    def _speaker_by_session(self, session_id: Any) -> Optional[Dict[str, Any]]:
        """兜底定位：返回该会话最近一条消息的说话者（仅在会话内唯一确定到人）。"""

        key = str(session_id or "").strip()
        if not key:
            return None
        record = self._latest_by_session.get(key)
        return record if isinstance(record, dict) else None

    # ── 同一轮只注入一次（去重）────────────────────────────────────────

    def _last_message_id(self, items: Any) -> str:
        """返回上下文里最后一条能映射的消息 ID（用于标识"这一轮"）。"""

        if not isinstance(items, list):
            return ""
        for item in reversed(items):
            if not isinstance(item, dict):
                continue
            for part in reversed(item.get("parts") or []):
                if not isinstance(part, dict):
                    continue
                text = part.get("text")
                if not isinstance(text, str):
                    continue
                found = _PLANNER_MSG_ID_RE.findall(text) + _MSG_ID_RE.findall(text)
                for message_id in reversed(found):
                    if str(message_id).strip() in self._recent:
                        return str(message_id).strip()
        return ""

    @staticmethod
    def _note_already_present(items: Any) -> bool:
        """上下文里是否已经有我们的注入抬头（宿主把上一回合的 items 带过来时命中）。"""

        if not isinstance(items, list):
            return False
        for item in items:
            if not isinstance(item, dict):
                continue
            for part in item.get("parts") or []:
                if isinstance(part, dict) and isinstance(part.get("text"), str):
                    if _NOTE_MARKER in part["text"]:
                        return True
        return False

    @staticmethod
    def _dedupe_key(stage: str, session_id: Any, turn_key: str) -> str:
        """去重键：同一阶段 + 同一会话 + 同一条消息 = 同一轮。

        拿不到消息 ID（走了会话兜底）时按 2 分钟时间桶去重，避免同一轮反复注入。
        """

        session = str(session_id or "").strip() or "-"
        if turn_key:
            return f"{stage}|{session}|{turn_key}"
        return f"{stage}|{session}|bucket{int(time.time() // 120)}"

    def _is_duplicate(self, key: str) -> bool:
        """该键在有效期内是否已经注入过。"""

        now = time.time()
        for old_key, ts in list(self._injected_keys.items()):
            if now - ts > _INJECT_DEDUPE_TTL:
                self._injected_keys.pop(old_key, None)
        return key in self._injected_keys

    def _mark_injected(self, key: str) -> None:
        """记录已注入，供同轮去重。"""

        self._injected_keys[key] = time.time()

    def _render_note(self, speaker: Dict[str, Any], label: str) -> str:
        """渲染注入文本（保证不含任何号码）。

        「态度 + 关心程度」全部取自配置里的三档文案，所以改配置就能调她的分寸。
        """

        name = self._sanitize_name(speaker.get("name"))
        rule = self._style_for(label)
        member_rule = self._style_for(_DEFAULT_LABEL)
        lines: List[str] = [f"{_NOTE_MARKER} · 只给你自己看，不要向别人解释或复述这份说明】"]
        lines.append(f"- 本条消息来自：{name}（你的{label}）。{rule}")
        if self._has_same_name(speaker):
            lines.append(
                f"- 注意：这里有不止一个人显示为「{name}」。"
                "当你在旧消息里分不清某句话是谁说的时，不要猜、也不要区别对待；"
                "只按上面「本条消息来自」这一行决定当前该怎么说话。"
            )
        # 说话者已经是群友档时，上面那行就是群友规则，不必再重复一遍
        if rule != member_rule:
            lines.append(f"- 其他所有人按普通群友对待：{member_rule}")
        lines.append(
            "- 这是你的内部认知，正常聊天时不用提它，也别主动给谁贴“档位”标签；"
            "但如果对方问起你们的关系，就自然承认、按关系说话，不用回避。"
        )
        return "\n".join(lines)

    def _has_same_name(self, speaker: Dict[str, Any]) -> bool:
        """同一会话里是否存在**别人**用了同一个显示名。"""

        name = str(speaker.get("name") or "").strip()
        session = str(speaker.get("session") or "")
        user_id = str(speaker.get("user_id") or "")
        if not name:
            return False
        for record in self._recent.values():
            if (
                str(record.get("session") or "") == session
                and str(record.get("name") or "").strip() == name
                and str(record.get("user_id") or "") != user_id
            ):
                return True
        return False

    def _diag_dump(self, items):
        """诊断：把上下文 items 的结构摘要打到 DEBUG 日志（只在 debug 级别开启时输出）。"""
        try:
            if not isinstance(items, list):
                self.ctx.logger.debug(f"[身份][诊断] items 类型={type(items).__name__}")
                return
            kinds = [it.get("item_type") for it in items if isinstance(it, dict)]
            texts = []
            for it in items:
                if not isinstance(it, dict):
                    continue
                for part in it.get("parts") or []:
                    if isinstance(part, dict) and isinstance(part.get("text"), str):
                        texts.append(part["text"])
            joined = "\n".join(texts)
            planner_ids = _PLANNER_MSG_ID_RE.findall(joined)
            bracket_ids = _MSG_ID_RE.findall(joined)
            matched = sum(1 for i in (planner_ids + bracket_ids) if i.strip() in self._recent)
            self.ctx.logger.debug(
                f"[身份][诊断] items={len(items)} 类型={kinds[:6]} 文本片段={len(texts)} "
                f"planner式命中={len(planner_ids)} 括号式命中={len(bracket_ids)} "
                f"可映射={matched} 最近={(planner_ids or bracket_ids or ['无'])[-1]}"
            )
        except Exception as exc:
            self.ctx.logger.debug(f"[身份][诊断] 失败: {exc}")

    def _append_note(self, kwargs: dict, note: str) -> Optional[str]:
        """把提示写进 hook 参数；返回写入位置描述，失败返回 None。"""

        items = kwargs.get("items")
        if isinstance(items, list):
            self._append_to_items(items, note)
            return "items/SystemMessageItem"
        if "extra_prompt" in kwargs:
            kwargs["extra_prompt"] = (kwargs.get("extra_prompt") or "") + note
            return "extra_prompt"
        return None

    @staticmethod
    def _append_to_items(items: list, note: str) -> None:
        """追加到最后一条 SystemMessageItem；没有则插到最前面新建一条。"""

        for item in reversed(items):
            if isinstance(item, dict) and item.get("item_type") == _ITEM_SYSTEM:
                parts = item.get("parts")
                if not isinstance(parts, list):
                    parts = []
                    item["parts"] = parts
                parts.append({"type": "text", "text": note})
                return

        items.insert(
            0,
            {
                "item_type": _ITEM_SYSTEM,
                "meta": {
                    "item_id": f"Alcpare-identity-{uuid.uuid4().hex}",
                    "logical_turn_id": None,
                    "timestamp": datetime.now().astimezone().isoformat(),
                },
                "parts": [{"type": "text", "text": note}],
            },
        )


def create_plugin() -> IdentityPlugin:
    """创建插件实例。"""

    return IdentityPlugin()
