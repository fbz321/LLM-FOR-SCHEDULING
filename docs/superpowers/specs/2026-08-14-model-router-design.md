# 设计文档：自适应模型路由（ModelRouter）

- 日期：2026-08-14
- 状态：已实现（实现与测试记录见 `docs/research/MULTI_AI_WORKFLOW.md`）
- 位置：`OnlineScheduling/bottleneck_reflection/`

## 1. 背景

`bottleneck_reflection` 系统用 LLM + Lean 内核做竞争比下界的瓶颈反省循环。当前 `LLMClient`
一次只能指定一个模型（`deepseek-chat` / `deepseek-v4-pro` / `deepseek-reasoner`），所有任务
（初始提议、瓶颈修复、策略重想）都打给同一个模型，没有按任务难度和结果做成本/质量权衡。

本设计引入一个可复用的 `ModelRouter`，作为该项目的基础工作逻辑：按任务类型分档选模型，
并在验证失败时把 flash 的结果升级给 pro 重做。

## 2. 目标与非目标

### 目标

- 新增 `ModelRouter`，持有 flash / pro 两个 `LLMClient`。
- 按任务类型分档：高频任务先试 flash，罕见高 stakes 任务直接 pro。
- flash 生成结果通过 Lean 验证失败时，升级到 pro（携带 flash 的失败代码 + 报错）。
- 记录路由统计（flash/pro 调用数、升级次数）。
- 把 orchestrator 主循环接入 router，同时保留 `--no-router` 回退到单模型。

### 非目标

- 不实现基于 prompt 复杂度打分的"智能"路由（易误判）。
- 不实现学习式/分类器式路由器。
- 不改 DSH（DeepSeek Harness）本身；本设计只作用于 Python 项目。
- 不复用 orchestrator 内更细的 `bottleneck_fix` prompt 作为升级 prompt（保持 router 通用）。

## 3. 模型约定

- flash = `deepseek-chat`（快、便宜）
- pro = `deepseek-reasoner`（慢、贵、推理强）

模型 ID 通过 CLI 参数可覆盖。

## 4. 架构

```
                ModelRouter
        ┌───────────┴───────────┐
   flash_client            pro_client        (两个 LLMClient)
        │                       │
        └──── generate_and_verify(task_type, messages, verify_fn) ────┘
                     │
              任务分档 + 验证失败升级
```

`ModelRouter` 职责单一：持有两个 client、按任务类型定档、在验证失败时把 flash 的结果 + 报错
喂给 pro 重做、记录统计。验证器（`check_lean_code`）和 `LLMClient` 的核心调用逻辑不动。

## 5. 组件

### 5.1 新文件 `model_router.py`

```python
@dataclass
class RouterResult:
    code: str                 # 最终（最优）代码
    result: object            # verify_fn 的返回（有 .compiles / .errors）
    model_used: str           # "flash" | "pro"
    escalated: bool           # 是否发生过 flash→pro 升级
    llm_calls: int            # 本轮消耗的 LLM 调用次数

class ModelRouter:
    def __init__(self, flash: LLMClient, pro: LLMClient,
                 routing: dict[str, str] | None = None): ...

    def generate_and_verify(self, task_type, messages, verify_fn) -> RouterResult: ...

    def generate(self, task_type, messages) -> str: ...  # 只生成不验证，返回代码文本；内部记录 stats

    @property
    def stats(self) -> dict: ...   # {"flash_calls": int, "pro_calls": int, "escalations": int}
```

### 5.2 任务分档表（默认）

| task_type | 初始档位 | 说明 |
|---|---|---|
| `initial_proposal` | `flash_first` | 频繁、便宜优先 |
| `bottleneck_fix` | `flash_first` | 频繁、便宜优先 |
| `strategy_rethink` | `pro` | 罕见、高 stakes |

档位语义：

- `flash_first`：先 flash 生成并验证；验证失败则升级 pro 重做。
- `pro`：直接 pro 生成（`generate_and_verify` 时也直接 pro 验证；`generate` 直接 pro 返回）。

未知 `task_type` 默认 `flash_first`（安全、便宜优先）。

## 6. 数据流

### 6.1 `generate_and_verify(task_type, messages, verify_fn)`

1. 查分档表得到初始档位。
2. `flash_first`：
   1. `flash.generate(messages)` 得代码。
   2. `result = verify_fn(code)`。
   3. 通过 → 返回 `RouterResult(code, result, "flash", escalated=False, llm_calls=1)`。
   4. 失败（或 `flash.generate` 抛异常）→ 构造升级 messages（见 6.2）→ `pro.generate(...)` →
      `verify_fn(...)` → 返回 `RouterResult(..., "pro", escalated=True, llm_calls=2)`。
3. `pro`：`pro.generate(messages)` → `verify_fn(...)` → 返回 `(model_used="pro", escalated=False)`。

pro 也失败时**不循环升级**，直接返回 pro 的结果；由 orchestrator 继续其既有的
bottleneck-fix / rethink 流程。

### 6.2 升级 messages 构造

```
原始 messages
  + {"role": "assistant", "content": flash 的失败代码}
  + {"role": "user", "content": (
       "上面的方案 Lean 编译失败，错误如下：\n"
       "<报错摘要>\n"
       "请修正后重新给出完整 Lean 代码。"
    )}
```

报错摘要取 `verify_fn` 返回对象的首条错误信息（截断到约 300 字符）。

## 7. orchestrator 集成

`orchestrator.py`：

- `self.llm` 替换为 `self.router`。
- 三个调用点接入：
  - `_propose_initial` + `_verify` → `router.generate_and_verify("initial_proposal", ...)`。
  - fix 循环的 `generate` + `check_lean_code` → `router.generate_and_verify("bottleneck_fix", ...)`。
  - `strategy_rethink` → `router.generate("strategy_rethink", ...)`（不验证，仍存为 `last_proposal`）。
- `main()` 新增参数：
  - `--flash-model`（默认 `deepseek-chat`）
  - `--pro-model`（默认 `deepseek-reasoner`）
  - `--no-router`（回退到原单模型行为）
- 结束时打印 router 统计。

## 8. `llm_client.py` 修正

- `deepseek-reasoner` 是推理模型：调用时**不传 `temperature`**（会报错/被忽略）、不传
  `thinking`；继续抽取 `reasoning_content`。
- `deepseek-chat` 保持现状（传 temperature）。

实现方式：在 `_call_deepseek_api` 中按模型分支 payload 构造。

## 9. 错误处理

- `flash.generate` 抛异常：捕获后走升级路径（与验证失败同）。
- `pro.generate` 抛异常：向上抛 `RuntimeError`（与现有 `LLMClient.generate` 一致），orchestrator
  照旧处理。
- 未知 `task_type`：`flash_first`，不报错。

## 10. 测试

`test_model_router.py`（`MockLLMClient` + 假 `verify_fn`）：

1. 分档正确：`strategy_rethink` 直接 pro，`initial_proposal` 走 flash。
2. flash 成功不升级。
3. flash 失败 → 升级 pro，且 pro 收到的 messages 含 flash 失败代码 + 报错。
4. pro 失败不循环升级，返回 pro 结果。
5. `stats` 计数正确。

另用 `--mock` 路径跑一遍 orchestrator 确认不崩。

## 11. 明确过的默认决策

- 分档默认：`initial_proposal` / `bottleneck_fix` 走 flash 先试，`strategy_rethink` 走 pro。
- 升级时 pro 只拿「原始 prompt + flash 失败代码 + 报错」，不复用 `bottleneck_fix` prompt。
