# 对抗搜索结果索引

> 本文件是稳定入口，不是逐次运行日志。详细历史见 [`EXPERIMENT_LOG.md`](EXPERIMENT_LOG.md)；Rudin 固定序列见 [`RUDIN2001_RESULTS.md`](RUDIN2001_RESULTS.md)；m=5 结构化搜索见 [`results/m5_structured/README.md`](results/m5_structured/README.md)。

## 当前结论

| 范围 | 结果 | 证据等级 |
|---|---|---|
| m=2 冒烟 | `3/2` | 精确 minimax 复现已知最优值 |
| m=4 FKT | `1707/1000 = 1.707` | 精确固定序列/搜索复现 |
| m=4 Rudin | `sqrt(3)-epsilon` | JSON 模板阈值检查；一般性结论见文献与 Lean 状态 |
| m=5 Rudin | `1.748334` | 71 作业、真实 prefix OPT、完整阈值博弈 PASS |
| m=7 Rudin | `1.7926675` | 57 作业、真实 prefix OPT、完整阈值博弈 PASS |
| m=6 Rudin | `1.7740979` 目标 | 仅完成 81/91 个 prefix OPT，**无最终结论** |

## 已完成的 m=5 有限负搜索

`results/m5_structured/README.md` 记录了所有证书和限制。已检查的有限邻域包括：

- singleton 位置、终端顺序和晚期交错；
- Type-2 单点及耦合尺寸网格；
- Type-3 缩放副本和插入 Type-2 形状块；
- 初始块、全 Type-2 共享参数等局部结构手术。

这些搜索均未超过 Rudin 的公开值。它们只排除各自明确列出的有限候选集，**不构成连续模型或更深策略的全局不可能性证明**。

## 方法边界

- 精确结果使用整数/有理数和真实离线 `OPT`；pseudo lower bound 不能替代真实竞争比。
- 启发式 DE、LLM 生成、MCTS 等只用于发现候选，不是证明。
- 固定序列和 state-dependent adaptive policy 分开报告；自适应证明必须穷举所有不等价调度器响应。
- “本次搜索最好值”不得写成某结构族的全局最优。

## 历史索引

- v2/v3/v4 的早期管线经验保留在 [`EXPERIMENT_LOG.md`](EXPERIMENT_LOG.md)。
- 自动生成的 pool Markdown 已删除；其 JSON 输入和生成脚本仍保留，可按需重建。
