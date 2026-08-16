# RESEARCH_PLAN — 在线调度下界研究（2026-08-08 起）

> 本文件是当前研究主线计划。历史计划见 task_plan.md（Rudin 形式化，已完成）。
> 背景调研见 outputs《在线调度下界-研究方向建议》；文献登记见 papers/_inbox/list.csv。

## 0. 现状与资产

- **Lean 库**：12 个全机械化定理（含 Rudin m=4 √3），0 sorry；runAlgorithm/layer_separation/OPT 基础设施齐全。
- **核心开放问题**：m=4 真实竞争比 ∈ [√3, 26/15]（下界 Rudin 2003 + Braun–Chung–Graham 2025 加性强化；上界 Chen et al. 1994）。间隙 ≈ 0.0013，20+ 年未破。
- **方法论先例**（均已下载到 _inbox）：Gabay2013（博弈论计算下界）、Böhm–Simon2022（DAG 证书 + Coq 认证，首个在线问题下界形式化认证）、Gormley2000（博弈树生成 adversary）。
- **形式化赛道窗口**：Pacut 的 Lean 竞争分析项目仍在设计阶段，我方实质领先，需尽快落纸。

## 1. 总策略：一条主攻线 + 两个保底 + 一条辅助线

| 线 | 内容 | 性质 |
|---|------|------|
| A | m=4 自动 adversary 搜索，目标 ρ ∈ (√3, 26/15] | 主攻（高风险高回报） |
| B | 机械化竞争分析库论文 | 保底（零数学风险） |
| C | Lean 验证 adversary 搜索可靠性（DAG 证书 soundness） | 保底（方法论原创） |
| D | 半在线小 m（known-sum m=3 / bin stretching >4/3） | 辅助产出线 |

决策点 P1（阶段 1 末）：A 有候选 → A+C 为主；A 停滞 → B+C 为主，A 转后台。

---

## 2a. Phase −1：基础修复（2026-08-08 插入，最高优先级）

> 发现旧 OPT 公理不一致（详见 findings.md 2026-08-08 重大条目）。
> 修复前所有旧下界定理形式上空真，必须先修基础再谈一切发表。

- [x] **−1.1** 不一致性证明（ProbeOPT.lean : False）
- [x] **−1.2** v2 基础：`scheduleLoads` + `optMakespan` + 5 定理（Basic.lean，已编译）
- [x] **−1.3** BraunGraham2025.lean 迁移（首个迁移样板）
- [ ] **−1.4** 遗留 24 文件语义迁移（当前仅验证了编译兼容，旧 OPT 仍在使用）（按规模排序：Rudin → Decreasing → ClassicOnline →
      GoS → Faigle → 其余；每迁一个跑单文件编译）
- [ ] **−1.5** 删除旧 OPT 公理 + 全库 `lake build` + find-gaps 零残留

## 2. Phase 0：热身与基础（08-08 → 08-22，两周）

- [x] **0.1 Braun2025 形式化规格**（findings.md）— 完成：数值仿真全通过 + 代数恒等式清单 + 打包路线
- [x] **0.2 形式化 Braun2025 Theorem 1**（`OnlineScheduling/LowerBounds/BraunGraham2025.lean`，已入湖：定义层+代数恒等式+Table 6 前缀 OPT+Table 7 打包（OPT=F）+主定理 `braun_asymptotic_lower_bound` 全部 0 sorry）
  - 构造：2(r+1) 个 4 元层（L 层全同、S 层 3 同 + plus 任务 S⁺ₖ=Sₖ+2Sₖ₋₁）+ 终任务 F，共 n=8r+9；
    长度按几何级数（比 2α²），α 选使极限为 √3
  - 路线：层长定义 → 强制调度追踪（论文 Table 3）→ OPT 打包上界（Table 4）→
    加性界 τ_A ≥ √3·τ_o − (2−√3)
  - 验收：lake build 通过；find-gaps 无新 axiom/sorry
  - 主定理实现 = r=1 实例（17 作业）自适应对抗：L₀/S₀/L₁/S₁ 偏离触发比率陷阱、
    S⁺₁ 陷阱由 `braun_prefix_additive_identity` 精确给出、clean 路径由 F 收尾
  - Theorem 2（有限 r 显式 ε_r，附录 Table 21/22）暂缓，视工作量
- [x] **0.2b（可选扩展）Braun2025 一般 r 强制归纳**：把 r=1 对抗推广为任意 r 的
      逐层归纳（每层 L_k 强制分散 + S_k 分散 + S⁺_k 陷阱 + F 收尾），对应论文
      n=8r+9 全参数族；r=1 实例已足以给出 Theorem 1 的 ∃ 陈述
  - 完成（2026-08-15）：`braun_asymptotic_lower_bound_general`（∀ r, ∀ alg,
    ∃ 前缀 σ ≤ σ_r 使 makespan ≥ √3·OPT − (2−√3)）+ 逐层不变式
    ∀i, Φ_k ≤ load_i（非均匀）+ 一般 k 陷阱（`braun_trap_Lk`/`braun_trap_Sk`）
    + 一般 k OPT witness（`braun_opt_Lk_trap_le`/`braun_opt_Sk_trap_le`）
    + 非均匀层分离（`braun_layer_separation_lb`/`braun_three_from_lb`）；
    0 sorry，全量 lake build 通过。论文字面"固定 σ_r 强制"表述不成立
    （在线算法可猜 Table 7 打包达到 OPT=F），形式化为自适应对抗 + 前缀 witness
- [ ] **0.3 证明 `graham_tightness`**（ListScheduling.lean 现有 axiom；LS 在 m(m−1)×1+[m] 上 ratio=2−1/m）
- [ ] **0.4 Böhm–Simon2022 认证架构笔记**（findings.md）：DAG 证书格式 → Lean 映射设计草案（为 C 铺路）
- [ ] **0.5 归档**：更新 LOWER_BOUND_TODOLIST.md（Rudin 状态、新增 Braun2025 条目）、docs/THEOREMS_ARCHIVE.md；git commit

**Phase 0 产出**：第 13 个形式化下界定理 + LS 紧例子 + 认证设计草案。

## 3. Phase 1：两线并行（08-23 → 09-20，四周）

### 线 A：adversary 搜索（2026-08-14 修订：从自由搜索转向"模板约束搜索"，见 findings.md 架构记录）
- [x] **A1'** 核心引擎（已完成）：`m4_search.py`（精确 minimax + 枚举 OPT + 对称/支配剪枝）+ `pattern_opt.py`（DE 尺寸优化）；k=3 自由搜索负结果 1.702 < √3（RESULTS.md）
- [ ] **A2'** 种子复现冒烟测试：`pattern_opt.py` 加 `--seed-structure`（rudin/braun/fkt），
      固定层模式只优化 2-5 个尺寸参数；验收：复现 FKT 1.707、Braun/Rudin √3（值 ≥ √3−1e-6）
- [ ] **A3'** 模板池：LLM 生成候选模板（层模式变体），固定结构 + DE 优化 + 粗筛；
      正/负结果都入 findings.md（参数、值、策略表）
- [ ] **A4** 独立 checker（第二实现，精确算术，断言**真实 OPT**，防 Tan–Li 伪界陷阱；输出打包证书）
- [ ] **A5** （条件触发）细化网格 / 策略迭代（fictitious play）

### 线 B：形式化论文
- [ ] **B1** 算法侧补全：ListScheduling 2−1/m 上界（Graham 1966）——使库成为"上下界完整"体系
- [ ] **B2** 框架统一：adaptive adversary 统一接口（策略 = 状态→作业 的函数 + 停止规则），整理 12+ 定理到统一叙述
- [ ] **B3** 论文骨架：intro（首个在线调度竞争分析机械化库）/ 清单表 / Rudin 案例深挖 / 与自动搜索的连接
- [ ] **B4** 投稿目标与时间：
  - CPP 2027：截稿约 2026-09 中旬（激进，视 B1-B3 进度）
  - **ITP 2027：截稿约 2027-02（主目标）**
  - JAR / J. Scheduling：rolling，随时可投

## 4. Phase 2：主攻（09-21 →，按 P1 决策分支）

**分支 A（搜索有候选）**：
- [ ] 独立穷举验证 → LLM 辅助结构归纳（聚类尺寸、识别层型）→ 参数化构造 + 证明草稿 → Lean 形式化
- [ ] 目标命题：∀ε>0（或显式 δ>0），∀alg，∃σ，makespan ≥ (√3+δ−ε)·OPT
- [ ] 投稿：J. Scheduling / TCS（Braun2025 同刊，直接对话）

**分支 B（搜索停滞）**：
- [ ] B+C 论文为主：机械化库 + verified adversary search 方法论
- [ ] A 降为背景任务（大网格/深度后台跑）

**方向 C 任务（两分支共用；2026-08-14 升级为"模板→优化→认证"闭环，详见 findings.md 架构记录）**：
- [ ] **C0** 模板层：LLM 生成候选对抗模板（层模式：层类型序列/每层作业数/尺寸递推关系），
      种子 = FKT/Rudin/Tan-Li/Braun 已知结构；每个模板固定结构、只优化 2-5 个自由尺寸参数
      （DE/minimax 求值，粗筛→精筛→有理化→独立 checker）
- [ ] **C1** Lean 定义证书类型：`GameTree`（节点=负载状态+待发作业，边=算法选择，叶=OPT 打包证书）
- [ ] **C2** soundness 定理：`value(tree) ≥ ρ → ∀ (alg : OnlineAlgorithm m), ∃σ, ratio alg σ ≥ ρ`
      （**只证一次**；所有模板降级为"填充 GameTree 数据"，不再逐模板写证明）
- [ ] **C3** OPT 枚举可靠性：`m4_search.opt()` 输出打包证书（每机作业清单）→ Lean 验证 `OPT ≤ c`；
      穷举搜索 → OPT 下界（两条都入 Lean）
- [ ] **C4** 实例层：幸存模板 → GameTree 结构体（尺寸参数填入）→ Lean checker 机械验证
      （每条边合法、每个叶打包有效），新模板 = 新数据，零新证明

**方向 C 关键设计决策**：证明成本只付一次（soundness），模板降级为数据。
逐模板写 Lean 证明不可行（Rudin 一个构造就 3700+ 行）；Böhm–Simon 2022 用 Coq
写单个 DAG checker 认证全部历史 bin-stretching 下界是同一招，我们补上 LLM 发现端。

**方向 D 辅助线（可选，视余力）**：
- [ ] known-sum m=3 或 bin stretching 下界改进，任选其一跑通"搜索→认证→形式化"闭环
  （bin stretching 有全套先例可抄：Gabay2013 的博弈构造 + Böhm 的 DAG 认证）

## 5. 里程碑

| 日期 | 里程碑 | 验收 |
|------|--------|------|
| 08-22 | Phase 0 完成 | BraunGraham2025 主定理 + graham_tightness 入湖，commit |
| 09-05 | A2' 种子复现 | 用 Braun/Rudin 层模板复现 √3，策略表存档 |
| 09-20 | A3' 模板池首轮 + B3 骨架 | 模板搜索结果（含负结果）入 findings；论文大纲 |
| ~09-12 | （可选激进）CPP 2027 | 若 B1-B3 就绪 |
| 10-31 | P1 决策执行一个月 | 分支 A：模板候选验证完；分支 B：C1-C2 完成 |
| ~2027-02 | ITP 2027 投稿 | B/C 论文成稿 |

## 6. 工程约定（每会话必做）

1. 更新 progress.md（会话日志）与 findings.md（数学发现/坑）
2. 搜索负结果与正结果同样记录（参数、网格、深度、根值）
3. 新定理 → THEOREMS_ARCHIVE.md 登记 → mutate_theorems.py 生成训练样本（喂养 LLM 管线）
4. 里程碑即 commit；大改动先单文件 `lake build`，再全量，最后 `find-gaps`

## 7. 风险登记

| 风险 | 概率 | 缓解 |
|------|------|------|
| A 搜不到 >√3（问题开放 20 年） | 高 | B/C/D 保底产出；负结果认证也可发表 |
| Braun2025 构造含论文未写明的细节 | 中 | 先数值仿真其 Table 3/4，对不上再查附录 |
| Pacut 项目抢先发表 | 中 | 优先保 ITP 2027 截稿；必要时先挂 arXiv preprint 确权 |
| 搜索爆炸（状态空间） | 中 | 降级策略迭代/MCTS；对称+支配剪枝；时间盒 |
| Lean/mathlib 版本漂移 | 低 | 锁定 4.33.0-rc1，升级仅在必要时 |