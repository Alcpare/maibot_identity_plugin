# -*- coding: utf-8 -*-
"""v1.0.3 专项验证：损坏的兜底文件不能让插件加载失败 + default_label 校验。"""
import importlib.util
import json
import pathlib
import sys
import tempfile
import time

P = pathlib.Path(__file__).resolve().parent.parent  # 插件根目录（可移植）
sys.path.insert(0, str(P.parent))
spec = importlib.util.spec_from_file_location("xiaoying_identity_v3", P / "plugin.py")
m = importlib.util.module_from_spec(spec)
sys.modules["xiaoying_identity_v3"] = m
spec.loader.exec_module(m)


class _Logger:
    def __init__(self):
        self.warnings = []

    def info(self, *a, **k): pass
    def debug(self, *a, **k): pass
    def error(self, *a, **k): pass

    def warning(self, *a, **k):
        self.warnings.append(a[0] if a else "")


class _Paths:
    def __init__(self, data_dir):
        self.data_dir = data_dir


class _Ctx:
    def __init__(self, data_dir):
        self.logger = _Logger()
        self.paths = _Paths(data_dir)


class TestPlugin(m.IdentityPlugin):
    """测试替身：把只读的 config 属性替换成我们自己的配置实例。"""

    _cfg = None

    @property
    def config(self):  # type: ignore[override]
        return self._cfg


def make_plugin(tmpdir, roster="1373558257 = 主人", default_label="群友"):
    p = TestPlugin.__new__(TestPlugin)
    p._ctx = _Ctx(tmpdir)
    cfg = m.IdentityPluginConfig()
    cfg.identity.roster = roster
    cfg.identity.default_label = default_label
    p._cfg = cfg
    p._labels = {}
    p._recent = {}
    p._latest_by_session = {}
    p._injected_keys = {}
    p._data_file = None
    p._last_save = 0.0
    return p


print("=== ① 损坏的 speakers.json：以前会抛异常 → on_load 炸掉插件 ===")
broken_cases = {
    "ts 是字符串": {"recent": {"a": {"user_id": "1", "ts": "不是数字", "name": "x"}},
                    "latest": {"s": {"user_id": "1", "ts": "abc"}}},
    "ts 是 None": {"recent": {"a": {"user_id": "1", "ts": None}}, "latest": {}},
    "ts 是字典": {"recent": {"a": {"user_id": "1", "ts": {"x": 1}}}, "latest": {}},
    "record 不是 dict": {"recent": {"a": "坏数据", "b": 123}, "latest": {"s": []}},
    "recent 是列表": {"recent": [1, 2, 3], "latest": None},
    "整个文件是数组": [1, 2, 3],
    "空对象": {},
}
for name, payload in broken_cases.items():
    with tempfile.TemporaryDirectory() as td:
        (pathlib.Path(td) / "speakers.json").write_text(
            json.dumps(payload, ensure_ascii=False), encoding="utf-8")
        p = make_plugin(td)
        try:
            p._rebuild_roster()
            p._load_persisted()            # 旧版这里会抛
            p._save_persisted(force=True)   # 写入路径也不能炸
            print(f"   {name:16} → ✅ 未抛异常（恢复 {len(p._recent)} 条）")
        except Exception as exc:  # noqa: BLE001
            print(f"   {name:16} → ❌ 抛了 {type(exc).__name__}: {exc}")
            raise SystemExit(1)

print()
print("=== ② 正常文件仍能恢复 ===")
with tempfile.TemporaryDirectory() as td:
    now = time.time()
    (pathlib.Path(td) / "speakers.json").write_text(json.dumps({
        "version": 1, "updated": now,
        "recent": {"good1": {"user_id": "1373558257", "name": "Alcpare", "session": "s1", "ts": now - 10}},
        "latest": {"s1": {"user_id": "1373558257", "name": "Alcpare", "session": "s1", "ts": now - 10}},
    }), encoding="utf-8")
    p = make_plugin(td)
    p._rebuild_roster()
    p._load_persisted()
    assert p._recent.get("good1"), "正常记录没恢复"
    assert p._latest_by_session.get("s1"), "会话快照没恢复"
    print(f"   ✅ 恢复 {len(p._recent)} 条映射 / {len(p._latest_by_session)} 个会话")

print()
print("=== ③ default_label 校验（无效值不能进提示词）===")
for bad in ("群主", "管理员", "", "  ", "GROUP"):
    with tempfile.TemporaryDirectory() as td:
        p = make_plugin(td, default_label=bad)
        p._rebuild_roster()
        label, hit = p._label_for("999999999")
        assert label in m._LABEL_RULES, f"default_label「{bad}」没校验 → {label!r}"
        assert label == "群友", f"应回落成群友，实际 {label!r}"
        print(f"   default_label={bad!r:10} → 档位 {label!r} ✓（无效值不会写进提示词）")
with tempfile.TemporaryDirectory() as td:
    p = make_plugin(td, default_label="朋友")
    p._rebuild_roster()
    print("   default_label='朋友'   → 档位", p._label_for("999999999")[0], "✓（合法值照常生效）")
    print("   名单内仍按名单走       → 档位", p._label_for("1373558257")[0], "✓")

print()
print("✅ v1.0.3 专项验证通过")
