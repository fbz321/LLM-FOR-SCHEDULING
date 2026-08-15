"""Braun 2025 专用验证器：把 LLM 生成的引理片段插入 BraunGraham2025.lean 副本，
单文件编译（`lake env lean`），复用 lean_verifier 的 LeanResult/LeanError 解析。

与 1.89 搜索那套的差别：
- 目标文件是已经迁到 v2 `optMakespan` 的 `BraunGraham2025.lean`（sound，0 sorry），
  不碰旧的 opaque `OPT` 公理。
- 验证的不是"完整独立文件"，而是"追加到现有文件末尾的声明片段"。
"""

import os
import subprocess
import tempfile

from lean_verifier import (
    LeanResult,
    LeanError,
    _filter_noise,
    _parse_errors,
    _has_error,
    _has_sorry,
)

# bottleneck_reflection/ 上一级是 OnlineScheduling/（Lean 项目根）
LEAN_PROJECT_PATH = os.environ.get(
    "LEAN_PROJECT_PATH", os.path.join(os.path.dirname(__file__), "..")
)
BRAUN_FILE = os.path.join(LEAN_PROJECT_PATH, "OnlineScheduling", "LowerBounds", "BraunGraham2025.lean")

LAKE_BIN = os.environ.get("LAKE_BIN", "lake")
LAKE_CMD = [LAKE_BIN, "env", "lean"]


def insert_fragment(src: str, fragment: str) -> str:
    """把 fragment 插到 namespace 结束的 `end` 之前。"""
    lines = src.split("\n")
    # 去掉尾部空行
    while lines and lines[-1].strip() == "":
        lines.pop()
    if lines[-1].strip() != "end":
        raise ValueError(
            f"BraunGraham2025.lean 尾部不是 `end`，实际为: {lines[-1]!r}"
        )
    body = "\n".join(lines[:-1]).rstrip()
    return body + "\n\n" + fragment.strip() + "\n\nend\n"


class BraunVerifier:
    """维护一个工作副本（原文 + 已成功的片段），对新片段做插入编译。"""

    def __init__(self, timeout: int = 180):
        with open(BRAUN_FILE, "r", encoding="utf-8") as f:
            self._base_src = f.read()
        self.current_src = self._base_src
        self.timeout = timeout
        self.committed = []  # 已成功提交的片段（按序，可直接合并回源文件）

    def reset(self) -> None:
        self.current_src = self._base_src
        self.committed = []

    def verify(self, fragment: str) -> LeanResult:
        """把 fragment 插入当前副本并编译；返回 LeanResult（不修改 current_src）。"""
        candidate = insert_fragment(self.current_src, fragment)
        return self._compile(candidate)

    def commit(self, fragment: str) -> None:
        """验证通过后调用：把 fragment 并入当前副本。"""
        self.current_src = insert_fragment(self.current_src, fragment)
        self.committed.append(fragment.strip())

    def _compile(self, src: str) -> LeanResult:
        fd, path = tempfile.mkstemp(suffix=".lean", prefix="_br_", dir=LEAN_PROJECT_PATH)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                f.write(src)

            result = subprocess.run(
                LAKE_CMD + [os.path.basename(path)],
                cwd=LEAN_PROJECT_PATH,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=self.timeout,
            )
            stderr = _filter_noise(result.stderr)
            stdout = _filter_noise(result.stdout)
            all_output = (stdout + "\n" + stderr).strip()

            success = (
                result.returncode == 0
                and not _has_error(all_output)
                and not _has_sorry(all_output)
            )
            errors = _parse_errors(all_output) if not success else []
            return LeanResult(
                compiles=success,
                raw_output=all_output,
                errors=errors,
                error_count=len(errors),
            )
        except subprocess.TimeoutExpired:
            return LeanResult(
                compiles=False,
                raw_output="Compilation timed out",
                errors=[LeanError(message="Lean compilation timed out")],
                error_count=1,
            )
        finally:
            try:
                os.unlink(path)
            except OSError:
                pass


if __name__ == "__main__":
    # 冒烟：插入一个平凡引理，验证管线跑通（离线，无 API）。
    v = BraunVerifier()
    r = v.verify("lemma braun_smoke : (1 : ℝ) + 1 = 2 := by norm_num")
    print(f"Compiles: {r.compiles}")
    print(f"Errors: {r.error_count}")
    if not r.compiles:
        print(r.raw_output[:500])
