# RESEARCH_PLAN — 在线调度下界研究（当前版：2026-08-31）

> 本文件只描述当前路线和未完成工作。历史施工计划与运行过程见 `docs/research/progress.md`；经典文献数值以 [`CLASSIC_ONLINE_LOWER_BOUNDS_STATUS.md`](CLASSIC_ONLINE_LOWER_BOUNDS_STATUS.md) 为准。

## 0. 当前状态

- Lean 库已有核心在线下界、Braun–Chung–Graham 2025 自适应加性构造和部分统一基础设施；具体声明、公理依赖与 `sorry` 状态以 [`THEOREMS_ARCHIVE.md`](../THEOREMS_ARCHIVE.md) 为准。
- 经典开放间隙：m=4 的真实竞争比在 `[sqrt(3), 26/15]`；渐近区间约为 `[1.88, 1.9201]`。
- m=5 的 Rudin 固定序列已用真实 prefix OPT 完整复核到 `1.748334`，但尚未产生超过文献值的新真实下界。详见 [`adversary_search/RUDIN2001_RESULTS.md`](../../adversary_search/RUDIN2001_RESULTS.md)。

## 1. 研究路线

| 线 | 内容 | 当前定位 |
|---|---|---|
| A | m=4 自适应对抗搜索，目标严格超过 `sqrt(3)` | 主攻，高风险 |
| B | 机械化竞争分析库与论文 | 稳定保底 |
| C | 通用策略 DAG / checker / Lean soundness | 方法论保底 |
| D | known-sum、bin stretching 等模型变体 | 可选辅助 |

如果 A 在明确的有限动作集和预算内停滞，则转为 B+C 主线；该决定不把有限负结果解释为连续模型不可能。

## 2. 当前工作包

### A：自适应搜索

- [x] 精确 minimax/OPT 原型和 FKT 冒烟。
- [x] 模板驱动的阈值粗筛管线。
- [ ] 固定有理阈值的 OR–AND reachability 求解器：完整状态 key、对称响应剪枝、迭代加深和策略 DAG 输出。
- [ ] 状态相关临界动作生成、progressive widening 和 CEGIS/escape-guided refinement。
- [ ] m=4 已知构造的校准：`3/2`、FKT 约 `1.707`、Rudin `sqrt(3)-epsilon`。
- [ ] 对任何 `tau > sqrt(3)` 候选进行 clean-cache、双实现、全策略分支认证。

技术规范见 [`adversary-search-workflow.md`](adversary-search-workflow.md)。

### B：库与论文

- [ ] 完成 List Scheduling `2 - 1/m` 上界的剩余 proof obligations。
- [ ] 整理核心模型与 known-sum、bin stretching、GoS 等变体的边界。
- [ ] 撰写稳定结果表、证据等级和可重放命令。

### C：认证基础设施

- [ ] **C1**：确认并稳定 Lean `GameTree`/策略 DAG 数据结构。
- [ ] **C2**：证明通用 soundness：有限策略树通过阈值 checker 可推出任意在线算法存在达到阈值的自适应前缀。
- [ ] **C3**：将 exact OPT 的 packing/容量证书接入 Lean；区分 `OPT <= c` 与 `OPT >= c` 两个方向。
- [ ] **C4**：把一个独立 Python 生成的 finite policy DAG 导入 Lean，完成端到端回放。

固定序列 exact verifier 已有实现，但不等同于 C1–C4 全部完成。

## 3. 证据等级

所有结果按以下层级记录：

```text
启发式候选 → 受限动作集 exact PASS → 独立有限策略证书
→ 参数化数学定理 → Lean kernel theorem
```

负结果必须同时记录动作集、深度、阈值、预算和 escape witness；不得把有限搜索的“最好值”写成全局最优。

## 4. 近期里程碑

| 顺序 | 里程碑 | 验收 |
|---:|---|---|
| 1 | OR–AND threshold solver | 通过 m=2/FKT 回归并输出 DAG |
| 2 | independent DAG checker | 穷举所有不等价调度器响应，真实 OPT |
| 3 | m=4 Rudin calibration | `sqrt(3)-epsilon` seed clean replay |
| 4 | critical actions + CEGIS | 每轮保存 manifest 与 escape witness |
| 5 | candidate gate | 仅 `tau > sqrt(3)` 且完整认证的候选进入 Lean |

## 5. 每次实验的最低记录

记录代码/输入哈希、机器数、动作菜单、深度、阈值、随机种子、状态数、OPT cache 命中率、证书/逃逸见证和证据等级。历史过程追加到 `progress.md`；最终结论写入对应专题结果文档，避免多处维护同一状态。
