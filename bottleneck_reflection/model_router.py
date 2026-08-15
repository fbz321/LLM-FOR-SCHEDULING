"""Adaptive model router: task-tiered model selection + verification-driven failover.

Holds a flash (cheap/fast) and a pro (slow/capable) LLMClient. For each task type it
picks an initial tier; when a flash result fails verification it escalates the same
task to pro with the flash failure + error as feedback.
"""

from dataclasses import dataclass
from typing import Callable, Optional

from llm_client import LLMClient


DEFAULT_ROUTING = {
    "initial_proposal": "flash_first",
    "bottleneck_fix": "flash_first",
    "strategy_rethink": "pro",
}


@dataclass
class RouterResult:
    code: str                 # 最终（最优）代码
    result: object            # verify_fn 的返回（有 .compiles / .errors / .raw_output）
    model_used: str           # "flash" | "pro"
    escalated: bool           # 是否发生过 flash→pro 升级
    llm_calls: int            # 本轮消耗的 LLM 调用次数


@dataclass
class _RouterStats:
    flash_calls: int = 0
    pro_calls: int = 0
    escalations: int = 0


def _error_summary(result, limit: int = 300) -> str:
    """Best-effort first-error summary from a verify result (LeanResult-like)."""
    errors = getattr(result, "errors", None) or []
    if errors:
        first = errors[0]
        msg = getattr(first, "message", "") or str(first)
        return msg[:limit]
    raw = getattr(result, "raw_output", "") or ""
    return raw.strip()[:limit] or "(no error detail)"


def _escalation_messages(messages: list, failed_code: str, summary: str) -> list:
    """Original messages + flash's failed code + error, for pro to fix."""
    return list(messages) + [
        {"role": "assistant", "content": failed_code},
        {"role": "user",
         "content": f"上面的方案 Lean 编译失败，错误如下：\n{summary}\n请修正后重新给出完整 Lean 代码。"},
    ]


class ModelRouter:
    """Routes a task to flash or pro, escalating flash failures to pro."""

    def __init__(self, flash: LLMClient, pro: LLMClient,
                 routing: Optional[dict] = None):
        self.flash = flash
        self.pro = pro
        self.routing = dict(DEFAULT_ROUTING)
        if routing:
            self.routing.update(routing)
        self._stats = _RouterStats()

    @property
    def stats(self) -> dict:
        return {
            "flash_calls": self._stats.flash_calls,
            "pro_calls": self._stats.pro_calls,
            "escalations": self._stats.escalations,
        }

    def _tier(self, task_type: str) -> str:
        return self.routing.get(task_type, "flash_first")

    def generate_and_verify(self, task_type: str, messages: list,
                            verify_fn: Callable[[str], object]) -> RouterResult:
        tier = self._tier(task_type)

        if tier == "pro":
            code = self.pro.generate(messages)
            self._stats.pro_calls += 1
            return RouterResult(code=code, result=verify_fn(code), model_used="pro",
                                escalated=False, llm_calls=1)

        # flash_first
        try:
            code = self.flash.generate(messages)
        except Exception as exc:  # flash 本身调用失败，也走升级
            return self._escalate(messages, "", f"flash 调用失败: {exc}", verify_fn)
        self._stats.flash_calls += 1

        result = verify_fn(code)
        if getattr(result, "compiles", False):
            return RouterResult(code=code, result=result, model_used="flash",
                                escalated=False, llm_calls=1)

        return self._escalate(messages, code, _error_summary(result), verify_fn)

    def _escalate(self, messages, failed_code, summary, verify_fn) -> RouterResult:
        esc = _escalation_messages(messages, failed_code, summary)
        pro_code = self.pro.generate(esc)
        self._stats.pro_calls += 1
        self._stats.escalations += 1
        return RouterResult(code=pro_code, result=verify_fn(pro_code), model_used="pro",
                            escalated=True, llm_calls=2)

    def generate(self, task_type: str, messages: list) -> str:
        """只生成不验证（用于 strategy_rethink 等），返回代码文本。"""
        tier = self._tier(task_type)
        if tier == "pro":
            self._stats.pro_calls += 1
            return self.pro.generate(messages)
        self._stats.flash_calls += 1
        return self.flash.generate(messages)
