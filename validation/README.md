# 验证集与评估脚本

> Step 1 — 固定验证集 + 客观评估指标  
> 创建时间: 2026-07-25

---

## 目录结构

```
validation/
├── README.md                      # 本文件
├── validation_gaps.json           # 30 个固定验证 gap（勿修改）
├── validation_summary.json        # 验证集元信息
├── generate_validation_set.py     # 验证集生成脚本（可重新运行）
├── eval.py                        # 评估脚本
└── results/                       # 各轮评估结果
    ├── round1_YYYYMMDD_HHMMSS/
    │   ├── summary.json
    │   ├── full_results.json
    │   └── failures.json          # 仅 --lean-check 时生成
    └── ...
```

---

## 验证集设计

### 定理来源

验证集使用的 **8 个定理均未在 R1-R7 训练数据中出现**：

| 定理 | 来源文件 | 难度 | Gaps | 证明特征 |
|------|----------|:--:|:--:|------|
| `makespan_ge_average` | Basic.lean | 中等 | 6 | calc block, field_simp, linarith |
| `opt_ge_both` | Basic.lean | 简单 | 1 | max_le 一步 |
| `runAlgorithm_mono` | Basic.lean | 困难 | 6 | induction, append rewrite |
| `sum_foldl_step` | Basic.lean | 困难 | 6 | induction, sum algebra |
| `load_mono_on_prefix` | Basic.lean | 简单 | 1 | delegate to lemma |
| `competitive_implies_bounded` | CompetitiveRatio.lean | 简单 | 1 | definitional (hc σ) |
| `competitive_ratio_ge_one` | CompetitiveRatio.lean | 困难 | 6 | multi-block: OPT bound, antisym |
| `known_sum_opt_bound` | Models/KnownSum.lean | 简单 | 3 | rw + apply existing lemma |

### 难度分布

| 难度 | 数量 | 说明 |
|:--:|:--:|------|
| 简单 | 6 | 1-2 行 tactic，基本 rewrites 和 apply |
| 中等 | 6 | calc blocks, field_simp, div 操作 |
| 困难 | 18 | induction, 多 block 推理, OPT bound 构造 |

### 覆盖的 Lean tactic 类型

`exact` / `apply` / `rw` / `simp` / `simpa` / `calc` / `field_simp` / `linarith` /
`nlinarith` / `induction'` / `have` / `let` / `refine` / `dsimp` / `Finset.sup'_le` /
`le_trans` / `max_le` / `div_le_div_of_nonneg_right` / `le_antisymm` / `by_cases`

---

## 评估指标

### pass@k (核心指标)

- `pass@1`: 对每个 gap 生成 1 次，至少 1 次正确的 gap 占比
- `pass@5`: 对每个 gap 生成 5 次，至少 1 次正确的 gap 占比

"正确"有两种定义：

| 模式 | 定义 | 需要 |
|------|------|------|
| `--lean-check` | Lean 编译通过 | lake, Lean 4 |
| 默认（无 flag） | 输出非空且无非法模式 | 无 |

### 辅助指标

| 指标 | 说明 |
|------|------|
| 平均生成长度 | 正常应在 50-500 chars；过短=空输出，过长=复述上下文 |
| 非法输出率 | 含自然语言解释、重复 import、markdown 块、注释解释等 |
| 空输出率 | 输出仅含空白或注释 |

### 非法输出检测规则

- 以自然语言开头（"Here is...", "The proof...", "Let me..."）
- 含重复 import（3+ import 语句）
- 含 markdown 代码块标记（``` ）
- 含解释性注释（-- Here / -- This / -- We）

---

## 使用方法

### 首次：生成验证集

```bash
cd /root/autodl-tmp/ai4math/validation
python3 generate_validation_set.py
# 生成 validation_gaps.json + validation_summary.json
```

### 评估单个模型（无 Lean 检查）

```bash
cd /root/autodl-tmp/ai4math/validation

# 评估 R1 最佳模型
CUDA_VISIBLE_DEVICES=0 python3 eval.py \
  --adapter /root/backups/round1 \
  --num-samples 5 \
  --output results/r1_baseline

# 评估 R6 模型
CUDA_VISIBLE_DEVICES=0 python3 eval.py \
  --adapter /root/backups/r6 \
  --num-samples 5 \
  --output results/r6_baseline
```

### 评估单个模型（含 Lean 编译检查）

```bash
CUDA_VISIBLE_DEVICES=0 python3 eval.py \
  --adapter /root/backups/round1 \
  --num-samples 5 \
  --lean-check \
  --lean-project /root/autodl-tmp/OnlineScheduling \
  --output results/r1_lean
```

### 比较两轮模型

```bash
# 查看两个 summary.json
python3 -c "
import json
for name in ['r1_baseline', 'r6_baseline']:
    d = json.load(open(f'results/{name}/summary.json'))
    print(f'{name}: pass_rate={d[\"pass_rate\"]:.1%}  '
          f'avg_len={d[\"avg_generated_length\"]:.0f}  '
          f'illegal={d[\"avg_illegal_output_rate\"]:.1%}')
"
```

---

## R8 训练前基线

在使用 R8 之前，建议先对 **R1（最佳）** 和 **R7（最差）** 分别评估，建立基线：

```bash
# 基线 1: R1 (loss=0.02, 88 samples)
python3 eval.py --adapter /root/backups/round1 --num-samples 5 --output results/r1_baseline

# 基线 2: R6 (loss=0.28, 201 samples, 73% Lean)
python3 eval.py --adapter /root/backups/r6 --num-samples 5 --output results/r6_baseline

# 基线 3: R7 (loss=0.29, 228 samples, mixed)
python3 eval.py --adapter /root/backups/r7 --num-samples 5 --output results/r7_baseline
```

R8 训练完成后，用同样的验证集评估，直接对比 summary.json 中的 `pass_rate`。

---

## 重要约束

1. **validation_gaps.json 一旦生成，禁止修改** — 这是固定验证集，任何修改都会破坏跨轮次可比性
2. **不要将验证集中的定理加入训练数据** — 这 8 个定理必须永远 held out
3. **评估时固定随机种子** — eval.py 使用 temperature=0.3，未设 seed（可后续添加 `--seed` 参数）
4. **备份** — 每次评估结果自动存入 `results/` 目录，不会覆盖已有内容
