# 训练实验报告

> 模型: DeepSeek-Math-7B-Base | 方法: QLoRA 4-bit rank=64, bnb
> GPU: NVIDIA RTX 4090 D, 24.5GB | Python 3.11, PyTorch 2.5.1+cu121

---

## 实验汇总

| 轮次 | 样本 | lr | epochs | avg loss | 时间 | 最佳模型? |
|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| R1 | 88 | 1e-4 | 5 | 0.23→**0.02** | 5:21 | ⭐ |
| R2 | 88 | 3e-5 | 8 | 0.27 | 4:56 | |
| R3 | 127 | 2e-5 | 6 | 0.33 | 8:26 | |
| R4 | 142 | 2e-5 | 5 | 0.33 | 4:30 | |
| R5 | 154 | 2e-5 | 5 | 0.32 | 4:47 | |
| R6 | 201 | 1.5e-5 | 5 | 0.28 | 6:08 | ⭐⭐ |
| R7 | 228 | 1.5e-5 | 5 | 0.29 | 6:49 | |

## 每轮数据组成

| 类型 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | 格式 | 有效? |
|------|:--:|:--:|:--:|:--:|:--:|:--:|:--:|------|:--:|
| gap_filling | 84 | 84 | 84 | 84 | 84 | 84 | 84 | Lean→Lean | ✅ |
| construction | 4 | 4 | 4 | 4 | 4 | 4 | 4 | NL→Lean | ✅ |
| typecheck_ok | — | — | 39 | 39 | 39 | 39 | 39 | Lean→Lean(同) | ❌ |
| M5_safe_gap | — | — | — | 15 | 15 | 15 | 15 | Lean→Lean | ✅ |
| counterexample | — | — | — | — | 12 | 12 | 12 | NL→NL | ❌ |
| M5_relaxed | — | — | — | — | — | 47 | 47 | Lean→Lean | ✅ |
| counterexample_v2 | — | — | — | — | — | — | 24 | NL→NL | ❌ |
| construction_recipe | — | — | — | — | — | — | 3 | NL→NL | ❌ |
| **总计** | 88 | 88 | 127 | 142 | 154 | 201 | 228 | | |

## R1 详细 (Best Model)

- 数据: `train_v1_alpaca.json`
- 84 M1+M5 gap-filling (Lean 代码补全)
- 4 construction (P2/P3/FKT/KS lower bounds)
- 学习率: 1e-4, 5 epochs
- 最终 loss: 0.02
- Adapter: `/root/backups/round1/adapter_model.safetensors` (572MB)
- 配置文件: `training/deepseek-math-7b_qlora_20260718_1643/sft.yaml`

## R6 详细 (Second Best)

- 数据: `train_v6_alpaca.json` (纯 Lean 数据)
- Lean→Lean 数据占比最高 (146/201 = 73%)
- 学习率: 1.5e-5, 5 epochs
- 平均 loss: 0.28
- Adapter: `/root/backups/r6/adapter_model.safetensors`

## 关键发现

### 1. 只有 Lean 代码数据有效

| 数据类型 | 输入→输出 | 对 loss 影响 |
|----------|----------|:--:|
| gap_filling | 不完整 Lean 证明 → 完整证明 | ✅ 降 loss |
| M5_relaxed | 删除 1 行的 Lean 证明 → 完整证明 | ✅ 降 loss |
| construction | NL 描述 → Lean 代码 | ✅ 有效但量少 |
| typecheck_ok | Lean 代码 → 相同代码 | ❌ 无信号 |
| counterexample | NL → NL | ❌ 稀释 |

### 2. 数据质量压倒数量

88 条纯 Lean gap-filling > 228 条混合数据。
R1 loss 0.02, R7 loss 0.29 — 质量下降 15 倍。

### 3. M5 自动生成经验

- 随机删除 tactic 行: 0% 通过率（tactic 之间有依赖）
- 安全白名单 (exact/simpa/linarith/...): 24 proofs → 15 gaps
- 放宽过滤 (只排除 induction/case/·): 7 proofs → 47 gaps
- 最优策略: 从 Basic.lean 提取完整 proof body，删除非结构化的独立行

### 4. 推理效果

R1 模型可以生成 Lean 代码，但 88 条数据不足以实现准确的证明补全。
需要更多高质量 Lean→Lean 训练数据。

## 诊断与改进建议

### 1. 不要用 train loss 直接比较不同轮次

R1 的 loss=0.02 很可能主要反映 88 条小数据上的强记忆，不一定代表泛化最好。R3-R7 的数据分布发生变化后，train loss 和模型实际证明能力不再可直接横向比较。

下一步应建立固定验证集，而不是继续只看训练 loss。

建议指标：
- `pass@1`：模型第一次生成是否能通过 Lean 检查
- `pass@5`：采样 5 次是否至少一次通过
- 平均生成长度：过长通常说明模型在复述上下文
- 非法输出率：是否输出解释文字、重复 import、截断证明等

### 2. 建立固定 Lean gap 验证集

从未进入训练集的定理中抽取 20-50 个 gap，固定保存为验证集。每轮模型都用同一批题评估，才能判断 R8/R9 是否真的变好。

验证集建议来源：
- `Basic.lean` 中较短的一步/两步证明
- `LowerBounds/DecreasingLowerBound.lean` 中已完整的 OPT 或 makespan 引理
- `Models/*.lean` 中短证明和定义展开证明

验证样本格式应统一为 Lean→Lean：

```lean
import OnlineScheduling.Basic
open OnlineScheduling

lemma target_statement ... := by
  -- hole
```

模型只输出 tactic/body，不输出自然语言解释。

### 3. 训练集只保留 Lean→Lean

下一轮训练建议去掉所有 NL→NL 样本，因为它们会稀释 Lean 证明补全能力。

保留：
- `gap_filling`
- `M5_safe_gap`
- `M5_relaxed`
- 输出为 Lean 代码的 construction 样本

移除或单独训练：
- `typecheck_ok`：Lean→同一 Lean，学习信号很弱
- `counterexample` / `counterexample_v2`：NL→NL，不服务于 Lean 补全
- `construction_recipe`：NL→NL，建议拆到另一个任务

### 4. M5 gap 生成策略

不要随机删除 tactic 行。随机删除会破坏 tactic 间依赖，导致样本目标与答案不匹配。

推荐只删除以下安全模式：
- `exact ...`
- `simpa ... using ...`
- `linarith` / `nlinarith`
- `omega`
- `ring` / `ring_nf`
- `norm_num`
- 单行 `rw [...]`
- 单行 `apply ...`

避免删除：
- `induction`
- `case`
- bullet 行：`·` / `.`
- `calc` 中间行
- 后续会被引用的 `have h_name`

### 5. R8 建议配置

建议从 base model 重新训练一个干净 R8，而不是继续混合 R7 数据。

推荐配置：
- 数据：150-300 条高质量 Lean→Lean gap
- 学习率：`5e-5` 或 `7e-5`
- epochs：`4-5`
- LoRA：沿用 rank=64, alpha=128
- cutoff_len：`2048`
- 每个 epoch 保存 checkpoint，并在固定验证集上评估 `pass@1/pass@5`

### 6. 短期优先级

1. 先写固定验证集和评估脚本。
2. 清理训练数据，只保留 Lean→Lean。
3. 生成更多安全 M5 gaps。
4. 训练 R8。
5. 用 pass rate 排名模型，而不是用 train loss 排名。

## 文件清单

```
ai4math/training/
├── r1 (deepseek-math-7b_qlora_20260718_1643)/
│   ├── sft.yaml      # 训练配置
│   └── metrics.txt   # loss=0.23, 5:21
├── r2/  lr=3e-5, 8 epochs, loss=0.27
├── r3/  +typecheck_ok, loss=0.33
├── r4/  +M5_safe_gap, loss=0.33
├── r5/  +counterexample, loss=0.32
├── r6/  +M5_relaxed, loss=0.28
└── r7/  +NL samples, loss=0.29

Server: /root/backups/
├── round1/  (R1 adapter, 572M)
├── round2/  (R2 adapter, 572M)
├── r3/  (R3 adapter, 572M)
...
├── r7/  (R7 adapter, 572M)
├── requirements.txt
└── environment.yml
```
