# NL→Lean 训练数据方案

> 创建: 2026-07-25 | 修订: 2026-07-25（v2，根据反馈修正）
> 状态: 待实施

---

## 核心想法

**训练模型将自然语言数学问题翻译为 Lean 4 形式化证明。**

当前 R1-R7 训练主要做 Lean→Lean gap-filling（补全 sorry），这训练出的模型只会"填空"，
不会"从零构造"。NL→Lean 训练让模型学会理解自然语言描述的数学问题，并生成完整的
Lean 形式化代码。

## 为什么可行（且为什么必须谨慎）

R1-R7 实验中已经有 4 条 construction 样本（NL→Lean），效果被标记为 ✅ 有效：

| 样本 | 输入 | 输出 |
|------|------|------|
| construction_P2_3over2 | "对 m=2，构造 adversary 使 LS makespan ≥ 3/2 * OPT" | Lean 代码 |
| construction_P3_5over3 | "对 m=3，构造 adversary 使 LS makespan ≥ 5/3 * OPT" | Lean 代码 |
| construction_Faigle_FKT | "对 m≥4，构造 FKT 下界 adversary" | Lean 代码 |
| construction_KnownSum_4over3 | "对 m=2 known-sum，构造 4/3 下界" | Lean 代码 |

**但必须吸取 NL→NL 的教训**：NL→NL 样本（counterexample）严重稀释了 Lean 能力。
NL→Lean 可以做，但必须保证：

1. **output 是可编译的 Lean 代码**（不是自然语言、不是伪代码）
2. **output 有真实的完整证明**（不是 axiom、不是 sorry、不是占位符）
3. **从短定理开始**，逐步增加复杂度
4. **比例不能太高**，Lean→Lean 始终是主体

## 数据源

项目中有 **45 个完整证明的定理**，每个都可以生成 NL→Lean 训练对。
**44 个 proof obligation 不用于 NL→Lean proof 训练**（没有 gold answer，会教模型输出 axiom）。

### 三层难度（仅使用完整证明的定理）

| 层级 | 数量（估计） | 示例 | 输出长度 |
|------|:--:|------|:--:|
| **L1 定义/引理** | ~15 | "证明 maxJobSize 非负" | 2-5 行 Lean |
| **L2 中等证明** | ~20 | "证明 makespan ≥ 平均负载" | 5-15 行 Lean |
| **L3 复杂定理** | ~10 | "证明 Graham 上界 2-1/m" | 15-50 行 Lean |

### NL→Lean proof obligation —— 不做

**不训练 "NL→Lean proof_obligation（无 gold answer）"。**

原因：
- 这类样本没有真实证明，输出是 `exact xxx_proof_obligation`，等于教模型偷懒
- 除非目标是生成 theorem skeleton（只输出 statement，不含 proof），否则不应混进 proof 训练
- 如果将来需要 theorem skeleton 能力，单独做一个 skeleton 数据集，不和 proof completion 混训

## R8 数据配比（修正版）

| 类型 | 占比 | 数量 | 作用 |
|------|:--:|:--:|------|
| **Lean→Lean** gap_filling + M5 | **70%** | 140-210 | 主体：保持 tactic 使用和 proof completion 能力 |
| **NL→Lean** L1/L2 | **20%** | 40-60 | 学会将短/中等数学问题翻译为 Lean |
| **NL→Lean** construction | **10%** | 20-30 | 学会构造反例/实例 |

总计约 **200-300 条**。如果 NL→Lean 不影响 Lean pass rate，再逐步提高比例。

## 实施顺序

```
Step 1: 用 validation/validation_gaps.json 建立 R1 baseline 的 pass@1/pass@5  ✅ 已完成
Step 2: 生成 30-50 条 L1/L2 NL→Lean 样本，只选完整证明，不选 proof obligation  ← 当前
Step 3: 训练 R8-clean：Lean→Lean 为主 (70%)，少量 NL→Lean (30%)
Step 4: 用同一个 validation set 比较 R1/R6/R8，不靠 train loss
Step 5: 如果 R8 没掉 Lean pass rate，逐步提高 NL→Lean 比例
```

## 预期效果

训练完成后，模型应能：

1. **gap-filling**: 保留原有核心能力，补全不完整的 Lean 证明
2. **形式化**: 给定 NL 描述的短/中等在线调度问题 → 生成正确的 Lean 定理陈述和证明
3. **不退化**: NL→Lean 的加入不应损害 Lean→Lean 的 pass rate

## NL→Lean 样本格式

```json
{
  "instruction": "将以下数学问题形式化为 Lean 4 证明。只输出 Lean 代码，不要解释。",
  "input": "在 m 台机器的在线调度问题中，证明 makespan（最大机器负载）
           至少是所有机器平均负载。即，任意负载分配下，最大负载不小于平均负载。",
  "output": "lemma makespan_ge_average (loads : Loads m) :\n    (Finset.sum Finset.univ loads) / (m : ℝ) ≤ makespan m loads := by\n  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m\n  ..."
}
```

关键约束：
- output 必须是通过 `lake build` 编译的完整 Lean 代码
- 不包含 `sorry`、`admit`、`*_proof_obligation`
- 不包含自然语言解释

## 长期目标

最终训练出一个 **在线调度理论的 AI 形式化助手**：
- 输入: 论文中的定理描述（自然语言 + 数学符号）
- 输出: 可编译的 Lean 4 形式化证明

这比单纯的 gap-filling 模型有用得多。

---

## R8 后路线：从格式改善到可编译 NL→Lean

R8 的主要进步是输出格式更干净：

- 固定 gap 验证集上，非空/干净输出率达到 100%
- 非法输出率从 R1 的 5.3% 降到 R8 的 0.7%
- 平均输出长度从 R1 的 934 降到 R8 的 845，复述倾向有所下降

但当前 R8 评估的 `lean_checked=false`，所以 100% pass 不能解释为 Lean 编译通过。`full_results.json` 中仍能看到若干明显不可编译模式，例如伪造不存在的 lemma、重复定义 theorem、引用不存在的辅助定义等。因此 R8 是“格式改善”的有效迭代，但还不是 NL→Lean 能力突破。

### 下一步目标

建立 **自然语言 → Lean → 编译检查** 的闭环。后续模型排名以 Lean-check pass rate 为主，而不是 train loss 或非空输出率。

### Step 1：新增 NL→Lean 固定验证集

新增 `validation_nl2lean.json`，包含 20-30 条 held-out 自然语言题目。

约束：
- 只选完整证明，不选 `*_proof_obligation`
- 不进入训练集
- 覆盖 L1/L2，少量 L3
- 每条样本包含 NL 输入、期望 Lean theorem/lemma、必要 import、gold output

验证任务示例：

```json
{
  "id": "nl2lean_val_makespan_ge_each",
  "type": "nl2lean",
  "input": "证明 makespan 不小于任意一台机器的负载。",
  "expected_name": "makespan_ge_each",
  "imports": ["Mathlib", "OnlineScheduling.Basic"]
}
```

### Step 2：升级 eval.py

`validation/eval.py` 需要支持两种任务：

- `lean_gap`：给 Lean 上下文和 hole，模型输出 proof body
- `nl2lean`：给自然语言描述，模型输出完整 Lean 文件或 theorem block

必须新增 Lean 编译检查：

- 将生成结果写入临时 `.lean`
- 在 Lean 项目环境中检查该文件
- 记录 `pass@1`、`pass@5`、错误类型和失败样例

评估字段建议：

```json
{
  "lean_checked": true,
  "pass@1": 0.0,
  "pass@5": 0.0,
  "syntax_error_rate": 0.0,
  "unknown_identifier_rate": 0.0,
  "timeout_rate": 0.0
}
```

### Step 3：增强非法输出检测

当前非法检测只能发现自然语言解释、markdown、重复 import 等浅层问题。需要新增更贴近 Lean 的规则：

- 重复定义同一个 `lemma` / `theorem`
- theorem 后缺少 `:= by`
- 出现明显伪造名字，如 `lemma_makespan_ge_average`
- 出现项目中不存在的常见幻觉名，如 `averageLoad`、`known_sum_average`
- proof body 缩进断裂
- 输出 unrelated theorem
- 输出超过合理长度后开始发散

这些规则不替代 Lean check，但能快速定位模型坏习惯。

### Step 4：重新评估 R1/R8

在训练 R9 前，必须先得到两组真实基线：

| 模型 | Lean gap pass@k | NL→Lean pass@k | 备注 |
|------|:--:|:--:|------|
| R1 | 待 Lean-check | 待 Lean-check | 小数据强记忆基线 |
| R8 | 待 Lean-check | 待 Lean-check | 格式改善基线 |

如果 R8 的 Lean gap 编译通过率低于 R1，应先修数据和评估，不急着扩大 NL→Lean 比例。

### Step 5：R9 数据配比

只有在 R8 不损害 Lean gap pass rate 的前提下，才训练 R9。

建议 R9 数据：

| 类型 | 占比 | 数量目标 |
|------|:--:|:--:|
| Lean→Lean gap / M5 | 60% | 180-300 |
| NL→Lean L1/L2 | 30% | 90-150 |
| NL→Lean construction | 10% | 30-50 |

总量目标：300-500 条高质量样本。

继续排除：

- NL→NL counterexample
- typecheck_ok 自复制样本
- proof_obligation 假证明

### Step 6：两阶段推理

直接 “自然语言 → 完整 Lean 证明” 难度较高。实际助手建议采用两阶段：

1. `NL → theorem skeleton`
   输出 import、namespace、变量、定理陈述，不输出 proof。
2. `theorem skeleton + context → proof body`
   使用 Lean→Lean proof completion 能力补证明。

训练数据也应逐步拆成两类：

- skeleton 数据：NL → Lean statement
- proof 数据：Lean statement/context → proof body

这样比一步生成完整文件更稳定，也更容易用 Lean error 做迭代修复。

### 最短可执行路线

1. 创建 `validation_nl2lean.json`，先做 20 条 held-out L1/L2。
2. 改 `eval.py`，支持 NL→Lean 和 Lean-check。
3. 跑 R1/R8 的真实 `pass@1/pass@5`。
4. 根据失败类型清理训练数据。
5. 训练 R9-clean。
6. 只用 Lean-check pass rate 排名模型。
