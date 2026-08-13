# 研究目标：在线平行机调度竞争比下界

> P | online, list | Cmax

## 问题

m 台同型并行机，作业逐个到达（无前瞻），到达后立即不可撤销分配到某台机器。目标是最小化最大完工时间 Cmax。性能用竞争比 ρ 衡量：对任何输入，Cmax(算法) ≤ ρ · OPT。

## 当前间隙

| 界 | 值 | 来源 |
|------|------|------|
| 下界 | **1.880…** | Rudin (2003), 渐近 |
| 上界 | **1.9201** | Bartal 等 / Fleischer-Wahl |
| **间隙** | **[1.880, 1.9201]** | |

## 两条路径

1. **提高下界**：构造更强 adversary，证明任何在线算法无法突破 1.90+
2. **降低上界**：设计比 Bartal 更优的算法，将竞争比降到 1.90 以下

## Lean 形式化进展

在 `OnlineScheduling/` 项目中：

- ✅ 基本定义和框架 (Basic.lean, 20/20)
- ✅ List Scheduling (Graham) 上界 
- ✅ Faigle-Kern-Turan 下界 (1+√2/2 ≈ 1.707)
- ✅ Rudin 渐近下界 (1.88)
- ✅ P2/P3 自适应 adversary 构造 (ClassicOnline)
- ✅ KnownSum P2 4/3 下界 (KnownSumP3)
- ✅ KnownSum P6 3/2 下界 (KnownSumM6)
- ⬜ Rudin m=4 √3 下界 (待证)
- ⬜ BinStretching 所有分支 (4 sorry)
- ⬜ KnownSum 小 m 下界系列

## LLM 辅助 Lean 方法演进

### 第一阶段：SFT 训练 (已废弃)
| 模型 | 基座 | 样本 | pass@3 |
|------|------|:--:|:--:|
| R9 | deepseek-math | 172 | 3.3% |
| R10 | deepseek-prover-v2 | 172 | 0% |

结论：7B 模型从少量样本学不到真实证明能力。废弃。

### 第二阶段：Bottleneck Reflection (当前)
受 Gilbert-Pollak 论文 (Ke et al., ICML 2026) 启发，不训练模型，
直接用 DeepSeek V4 Pro API + Lean kernel 验证 + 瓶颈反省循环。

核心架构：`bottleneck_reflection/` 目录。
- LLM 提出 adversary 参数 → 填入 Lean 模板 → Lean kernel 验证 → 反馈循环
- 关键模块：`OnlineScheduling/LowerBounds/Lemmas.lean` (已编译)
- 当前卡点：`OnlineScheduling/Template.lean` 参数化模板修复中
