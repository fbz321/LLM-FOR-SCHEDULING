"""Tests for llm_client.build_deepseek_payload — zero network."""
from llm_client import build_deepseek_payload

MSG = [{"role": "user", "content": "x"}]


def test_reasoner_omits_temperature_and_thinking():
    p = build_deepseek_payload("deepseek-reasoner", MSG, 4096, 0.3)
    assert "temperature" not in p
    assert "thinking" not in p
    assert p["max_tokens"] == 4096
    assert p["model"] == "deepseek-reasoner"


def test_chat_has_temperature_no_thinking():
    p = build_deepseek_payload("deepseek-chat", MSG, 4096, 0.3)
    assert p["temperature"] == 0.3
    assert "thinking" not in p


def test_v4_pro_disables_thinking():
    p = build_deepseek_payload("deepseek-v4-pro", MSG, 4096, 0.3)
    assert p["temperature"] == 0.3
    assert p["thinking"] == {"type": "disabled"}


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print(f"PASS {name}")
    print("all tests passed")
