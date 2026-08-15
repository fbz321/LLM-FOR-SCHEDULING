"""Tests for model_router.ModelRouter — zero network, zero Lean."""
import types

from model_router import ModelRouter


class FakeClient:
    def __init__(self, responses):
        self.responses = list(responses)   # 每次 generate 弹出一个
        self.calls = []                    # 记录每次收到的 messages

    def generate(self, messages):
        self.calls.append(list(messages))
        return self.responses.pop(0)


def ok_verify(code):
    return types.SimpleNamespace(compiles=True, errors=[], raw_output="")


def fail_verify(code):
    return types.SimpleNamespace(
        compiles=False,
        errors=[types.SimpleNamespace(message="type mismatch at line 3")],
        raw_output="x.lean:3:4: error: type mismatch",
    )


def test_flash_success_no_escalation():
    flash = FakeClient(["GOOD"])
    pro = FakeClient(["PRO"])
    r = ModelRouter(flash, pro)
    rr = r.generate_and_verify("initial_proposal", [{"role": "user", "content": "hi"}], ok_verify)
    assert rr.model_used == "flash"
    assert rr.escalated is False
    assert rr.llm_calls == 1
    assert pro.calls == []


def test_flash_failure_escalates_with_context():
    flash = FakeClient(["BAD code"])
    pro = FakeClient(["FIXED code"])
    r = ModelRouter(flash, pro)
    msgs = [{"role": "user", "content": "prove it"}]
    rr = r.generate_and_verify("bottleneck_fix", msgs, fail_verify)
    assert rr.model_used == "pro"
    assert rr.escalated is True
    assert rr.llm_calls == 2
    pro_msgs = pro.calls[0]
    assert pro_msgs[0] == msgs[0]
    assert any("BAD code" in m["content"] for m in pro_msgs)
    assert any("type mismatch" in m["content"] for m in pro_msgs)


def test_strategy_rethink_goes_pro_directly():
    flash = FakeClient(["FLASH"])
    pro = FakeClient(["PRO"])
    r = ModelRouter(flash, pro)
    code = r.generate("strategy_rethink", [{"role": "user", "content": "rethink"}])
    assert code == "PRO"
    assert flash.calls == []


def test_pro_failure_does_not_loop():
    flash = FakeClient(["BAD"])
    pro = FakeClient(["STILL BAD"])
    r = ModelRouter(flash, pro)
    rr = r.generate_and_verify("initial_proposal", [{"role": "user", "content": "x"}], fail_verify)
    assert rr.model_used == "pro"
    assert rr.escalated is True
    assert rr.llm_calls == 2
    assert len(pro.calls) == 1


def test_unknown_task_defaults_flash_first():
    flash = FakeClient(["GOOD"])
    pro = FakeClient(["PRO"])
    r = ModelRouter(flash, pro)
    rr = r.generate_and_verify("mystery_task", [{"role": "user", "content": "x"}], ok_verify)
    assert rr.model_used == "flash"
    assert pro.calls == []


def test_stats_counting():
    flash = FakeClient(["BAD", "BAD"])
    pro = FakeClient(["GOOD", "GOOD"])
    r = ModelRouter(flash, pro)
    r.generate_and_verify("initial_proposal", [{"role": "user", "content": "1"}], fail_verify)
    r.generate_and_verify("bottleneck_fix", [{"role": "user", "content": "2"}], fail_verify)
    assert r.stats == {"flash_calls": 2, "pro_calls": 2, "escalations": 2}


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print(f"PASS {name}")
    print("all tests passed")
