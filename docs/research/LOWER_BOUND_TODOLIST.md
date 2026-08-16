# 下界实例与证明 — 待完成清单

> 目标：覆盖所有"给出对抗实例并证明下界"的 axiom/trivial 占位。
> 不含算法上界（ListScheduling 分析、M2 算法）。

---

## 0. 基础设施（前置依赖）

| # | 文件 | 定理/引理 | 占位方式 | 说明 |
|---|------|----------|:---:|------|
| 0.1 | Basic.lean:169 | `opt_ge_max_job` | axiom | 最大作业 ≤ OPT |
| 0.2 | Basic.lean:170 | `opt_ge_avg_load` | axiom | 平均负载 ≤ OPT |
| 0.3 | Basic.lean:189 | `opt_monotone` | axiom | OPT 对前缀单调 |
| 0.4 | Basic.lean:190 | `opt_le_of_schedule` | axiom | 任意可行调度给出 OPT 上界 |

**依赖关系**：几乎所有下界证明都需要这 4 条。

---

## 1. 经典通用下界（对所有确定性算法成立）

### 1.1 P2||Cmax — 下界 3/2 ✅

文件：[ClassicOnline.lean](OnlineScheduling/OnlineScheduling/LowerBounds/ClassicOnline.lean)

| # | 状态 | 说明 |
|---|:---:|------|
| `p2_Cmax_lower_bound` | ✅ 已证 | 自适应对手：`[1,1]` → 同机则停(ratio≥2)，异机则续`[2]`(ratio=3/2) |

---

### 1.2 P3||Cmax — 下界 3/2 ✅

文件：[ClassicOnline.lean](OnlineScheduling/OnlineScheduling/LowerBounds/ClassicOnline.lean)

| # | 状态 | 说明 |
|---|:---:|------|
| `p3_Cmax_lower_bound` | ✅ 已证 | 自适应对手：`[1,1,1]` → 全异则续`[2]`(ratio=3/2)，否则停(ratio≥2) |

> 注：紧下界 5/3 需要更复杂的层次化对手（FKT 方法）。当前证明给出有效的 3/2。

---

### 1.3 P4||Cmax 及以上 — 见 Faigle / Rudin

文件：[ClassicOnline.lean](OnlineScheduling/OnlineScheduling/LowerBounds/ClassicOnline.lean)

P4 的 LS 紧例子（7/4）已移除。通用下界由 FKT (`1+√2/2`) 和 Rudin (`√3`, `1.88`) 覆盖。

---

### 1.4 FKT 下界 — `1 + √2/2 ≈ 1.707` (m ≥ 4)

文件：[Faigle.lean](OnlineScheduling/OnlineScheduling/LowerBounds/Faigle.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 1.4.1 | `opt_of_identical_jobs` | axiom | m 个相同作业的 OPT = 单个大小 |
| 1.4.2 | `loads_are_multiples` | axiom | 处理 m 个相同作业后，负载是作业大小的整数倍 |
| 1.4.3 | `layer_separation` | axiom | 一层 m 个相同作业：要么 ratio≥2，要么每台恰好一个 |
| 1.4.4 | `layer_separation_from_base` | axiom | 有统一基础负载时的层次分离 |
| 1.4.5 | `faigle_kern_turan_lower_bound` | axiom | **主定理**：存在 σ 使 ratio ≥ fkt_constant |

实例构造思路已在 ROADMAP Step 1 中描述（2a + 2b + final job = 1）。

---

### 1.5 Rudin 下界

文件：[Rudin.lean](OnlineScheduling/OnlineScheduling/LowerBounds/Rudin.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 1.5.1 | `rudin_m4_lower_bound` | ✅ 已证 | m=4: ratio ≥ √3 − ε（对所有 ε>0），`rudin_m4_adversary_exists` 真证明；构造 = type-1/type-2 交替层 + 收尾 2A₀（含终止层夹逼修复，见 task_plan Phase 0） |
| 1.5.2 | `rudin_asymptotic_adversary_exists` | axiom | m ≥ 3454: ratio ≥ 1.88；**阻塞于文献缺口**——Rudin 博士论文构造，Fleischer-Wahl 仅引用无细节 |

**实例已形式化**：Type-1/Type-2 层次序列 + 递推分析（Rudin.lean 3700+ 行，`lake build` 通过）。

---

## 2. 变种模型下界

### 2.1 Bin-Stretching — 下界 4/3

文件：[BinStretchingLowerBound.lean](OnlineScheduling/OnlineScheduling/LowerBounds/BinStretchingLowerBound.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 2.1.1 | `bs_first_phase_dichotomy` | axiom | 第一阶段后：要么全均匀，要么存在负载≥2/3 |
| 2.1.2 | `bs_phase2a_forces_bound` | axiom | 有重载机器时 → ratio ≥ 4/3 |
| 2.1.3 | `bs_phase2b_forces_bound` | axiom | 全均匀时 → ratio ≥ 4/3 |
| 2.1.4 | `bin_stretching_lower_bound_four_thirds` | axiom | **主定理** |

实例已写出：phase1 = m×1/3, phase2a = m×2/3, phase2b = [1]

---

### 2.2 Grade of Service — 下界 5/3 (m=2) ✅

文件：[GoSLowerBound.lean](OnlineScheduling/OnlineScheduling/LowerBounds/GoSLowerBound.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 2.2.1 | `gos_opt_A` | ✅ 已证 | OPT(分支 A) = 1 |
| 2.2.2 | `gos_opt_B1` | ✅ 已证 | OPT(分支 B1) = 3 |
| 2.2.3 | `gos_opt_B2a` | ✅ 已证 | OPT(分支 B2a) = 3 |
| 2.2.4 | `gos_opt_B2b` | ✅ 已证 | OPT(分支 B2b) = 6 |
| 2.2.5 | `gos_online_lower_bound_five_thirds` | ✅ 已证 | **主定理**：任意 GoS 算法 ∃ 序列 ratio ≥ 5/3（GoSAlgorithm2 模型，Park-Chang-Lee Lemma 1 自适应 adversary） |

实例已写出：4 条分支序列。

---

### 2.3 Known Sum P2 — 下界 4/3

文件：[KnownSumP3.lean](OnlineScheduling/OnlineScheduling/LowerBounds/KnownSumP3.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 2.3.1 | `ks2_case1_opt` | axiom | OPT(`[1/3,1/3,2/3,2/3]`) = 1 |
| 2.3.2 | `ks2_case2_opt` | axiom | OPT(`[1/3,1/3,1,1/3]`) = 1 |
| 2.3.3 | `ks2_first_two_split` | axiom | 处理两个 1/3 后的二分叉 |
| 2.3.4 | `ks2_case1_makespan_ge` | axiom | 同机分支 → makespan ≥ 4/3 |
| 2.3.5 | `ks2_case2_makespan_ge` | axiom | 异机分支 → makespan ≥ 4/3 |
| 2.3.6 | `ks2_known_sum_lower_bound` | axiom | **主定理** |

实例已写出：`ks2_case1`, `ks2_case2`。

---

### 2.4 Known Sum P3 — 下界 `1 + (√19−2)/6 ≈ 1.3929`

文件：[KnownSumP3Three.lean](OnlineScheduling/OnlineScheduling/LowerBounds/KnownSumP3Three.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 2.4.1 | `ks3_optimal_eps_pos` | axiom | 最优 ε > 0 |
| 2.4.2 | `ks3_optimal_eps_lt_one_sixth` | axiom | 最优 ε < 1/6 |
| 2.4.3 | `ks3_opt_A` | axiom | OPT(实例 A) = 1 |
| 2.4.4 | `ks3_known_sum_lower_bound` | axiom | **主定理** |

实例含参数 ε 已写出。

---

### 2.5 Known Sum m=6 — 下界 3/2

文件：[KnownSumM6.lean](OnlineScheduling/OnlineScheduling/LowerBounds/KnownSumM6.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 2.5.1 | `ks6_opt_A` | axiom | OPT(实例 A) = 1 |
| 2.5.2 | `ks6_opt_B` | axiom | OPT(实例 B) = 3/2 |
| 2.5.3 | `ks6_phase1_dichotomy` | axiom | 第一阶段二分叉 |
| 2.5.4 | `ks6_lower_bound_three_halves` | axiom | **主定理** |

实例已写出：phase1 = 6×3/4, phase2a = 6×1/4, phase2b = [3/2]

---

### 2.6 Known Sum m=3,4,5 — 各一下界

文件：[KnownSumSmallM.lean](OnlineScheduling/OnlineScheduling/LowerBounds/KnownSumSmallM.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 2.6.1 | `ks_m3_lower_bound` | axiom | m=3: ratio ≥ `1+(−3+√129)/6` |
| 2.6.2 | `ks_m4_lower_bound` | axiom | m=4: ratio ≥ `1+(−4+√160)/6` |
| 2.6.3 | `ks_m5_lower_bound` | axiom | m=5: ratio ≥ `1+(−5+√193)/6` |
| 2.6.4 | `ks_m6_lower_bound` | axiom | m=6: ratio ≥ 3/2 |

**实例均未显式写出**，ratio 常数已定义。

---

### 2.7 Known Sum 通用 — 下界 4/3

文件：[KnownSumLowerBound.lean](OnlineScheduling/OnlineScheduling/LowerBounds/KnownSumLowerBound.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 2.7.1 | `known_sum_m2_lower_bound_four_thirds` | ✅ 已证 | **主定理** |

---

### 2.8 Decreasing Job Sizes — 下界 7/6 (m=2), ~1.18 (m=3)

文件：[DecreasingLowerBound.lean](OnlineScheduling/OnlineScheduling/LowerBounds/DecreasingLowerBound.lean)

| # | 定理/引理 | 占位方式 | 说明 |
|---|----------|:---:|------|
| 2.8.1 | `dec2_opt` | ⚠️ 部分证 | OPT(`[3,3,2,2,2]`) = 6（有骨架但缺推理） |
| 2.8.2 | `dec2_lower_bound` | `trivial` | **主定理**：任意算法 ratio ≥ 7/6 |
| 2.8.3 | `dec3_opt` | ⚠️ 部分证 | OPT = 1（有骨架但缺推理） |
| 2.8.4 | `dec3_lower_bound` | `trivial` | **主定理**：任意算法 ratio ≥ `(1+√37)/6` |

实例已写出：`dec2_instance = [3,3,2,2,2]`, `dec3_instance` 含参数 x。

---

### 2.9 伪下界 (Tan & Li 2015) — m=4 ✅ / m=5 ✅ / m=6 ✅ / 通用 m ✅

文件：[PseudoLowerBound.lean](OnlineScheduling/OnlineScheduling/LowerBounds/PseudoLowerBound.lean)
m=5：文件：[PseudoLowerBoundM5.lean](OnlineScheduling/OnlineScheduling/LowerBounds/PseudoLowerBoundM5.lean)
m=6：文件：[PseudoLowerBoundM6.lean](OnlineScheduling/OnlineScheduling/LowerBounds/PseudoLowerBoundM6.lean)
通用 m：文件：[PseudoLowerBoundGeneral.lean](OnlineScheduling/OnlineScheduling/LowerBounds/PseudoLowerBoundGeneral.lean)

> 只用弱下界（平均负载 LB1、最大作业 LB2，m=4 时 LB3 不生效）无法证明竞争比低于 1+γ_m。

| # | 定理 | 状态 | 说明 |
|---|------|:---:|------|
| 2.9.1 | `m4_pseudo_lower_bound` | ✅ | m=4: 1+11/15 = 26/15，5 阶段自适应 adversary |
| 2.9.2 | `m5_pseudo_lower_bound` | ✅ | m=5: 1+37/48 = 85/48，q=1，β5 = 37/48 |
| 2.9.3 | `m6_pseudo_lower_bound` | ✅ | m=6: 1+4/5 = 9/5，q=1，β6 = 4/5 |
| 2.9.4 | `pseudo_lower_bound_general` | ✅ | 通用 m（m≥4）：f_i/g_i/x_i 解析恒等式、I^(m)/q_m/β_m/γ_m=min(β_m,α)、Lemma 2.6 三条不等式、σ1–σ5 的 PseudoLBGen 上界、5 阶段机级 adversary；比率 1+γ_m |

---

## 3. 边界：Graham 紧例子

文件：[ListScheduling.lean](OnlineScheduling/OnlineScheduling/Algorithms/ListScheduling.lean)

| # | 定理 | 占位方式 | 说明 |
|---|-----|:---:|------|
| 3.1 | `graham_tightness` | axiom | LS 在 `m(m−1)×1 + [m]` 上 ratio = 2−1/m |

> 这个不属于通用下界（它只针对 LS），但它是经典的最坏情况构造，对训练模型生成对抗实例有参考价值。

---

## 统计

| 类别 | 文件数 | 已完成 | 待补 | 备注 |
|------|:---:|:---:|:---:|------|
| 基础设施 | 1 | 4 axiom (留作公理) | 0 | 4条 OPT 公理保持不变 |
| 通用下界 | 3 | 3 (ClassicOnline P2/P3, Faigle) | 1 (Rudin) | ClassicOnline P4 已移除 |
| 变种模型 | 8 | 6 (BinStretching, GoS, KnownSumP3, KnownSumM6, KnownSumLowerBound, Decreasing) | 2 | 剩余 KnownSumP3Three / KnownSumSmallM（已知总和，范围外） |
| 边界 | 1 | 0 | 1 | Graham tightness (LS专有) |
| **合计** | **13** | **9** | **4** | |

---

## 已完成（12 个定理，全部自适应，0 sorry）

| 文件 | 定理 | 比率 | 关键技术 |
|------|------|:---:|------|
| ClassicOnline | `p2_Cmax_lower_bound` | 3/2 | 自适应，Fin 2 全覆盖 |
| ClassicOnline | `p3_Cmax_lower_bound` | 3/2 | 自适应，Fin 3 Finset 全覆盖 |
| Faigle | `faigle_kern_turan_lower_bound` | 1+√2/2 | 两层 layer_separation，鸽笼原理 |
| BinStretching | `bin_stretching_lower_bound_four_thirds` | 4/3 | 复用 Faigle.layer_separation |
| KnownSumP3 | `ks2_known_sum_lower_bound` | 4/3 | 二分叉，Fin 2 全覆盖 |
| KnownSumM6 | `ks6_lower_bound_three_halves` | 3/2 | 复用 Faigle.layer_separation |
| PseudoLowerBoundM5 | `m5_pseudo_lower_bound` | 1+37/48 | 5 阶段自适应，复用 Faigle.layer_separation |
| PseudoLowerBoundM6 | `m6_pseudo_lower_bound` | 1+4/5 | 5 阶段自适应（阶段3有5个作业），复用 Faigle.layer_separation |
| PseudoLowerBoundGeneral | `pseudo_lower_bound_general` | 1+γ_m | 通用 m：5 阶段自适应，Phase34Inv 不变式归纳，复用 Faigle.layer_separation |
| KnownSumLowerBound | `known_sum_m2_lower_bound_four_thirds` | 4/3 | 已知总和 m=2，复用 ks2_known_sum_lower_bound 二分叉 |
| GoSLowerBound | `gos_online_lower_bound_five_thirds` | 5/3 | GoSAlgorithm2 模型，Park-Chang-Lee Lemma 1 自适应（A/B1/B2a/B2b 四分支） |
| BraunGraham2025 | `braun_asymptotic_lower_bound` | **加性** √3·OPT−(2−√3)（渐近 √3） | Braun–Chung–Graham 2025 Theorem 1（m=4）：r=1 实例自适应对抗，L₀/S₀/L₁/S₁ 偏离陷阱 + S⁺₁ 精确加性陷阱（braun_prefix_additive_identity）+ F 收尾（braun_additive_identity）；前缀 OPT 用 Table 6/7 打包（braun_opt_prefix_Sp / braun_opt_eq_F） |
| BraunGraham2025 | `braun_asymptotic_lower_bound_general` | **加性** √3·OPT−(2−√3)，∀ r（前缀 σ ≤ σ_r，n=8r+9 全参数族） | 论文 Table 3 逐层强制归纳（RESEARCH_PLAN 0.2b）：非均匀不变式 ∀i, Φ_k ≤ load_i，L_k/S_k/S⁺_k 一般陷阱（braun_trap_Lk/Sk）+ 一般 OPT witness + 非均匀层分离（braun_layer_separation_lb/braun_three_from_lb）；r=1 定理为其推论 |

## 待完成（4 个）

| 优先级 | 文件 | 复杂度 | 阻塞原因 |
|:---:|------|:---:|------|
| ★★ | KnownSumP3Three | 高 | 参数化 eps，多分支 |
| ★★ | KnownSumSmallM | 中 | 需先写出具体实例 |
| ★★★ | Rudin | 最高 | 层次递推，Type-1/Type-2 层，递推不等式 |
| ★ | Graham tightness | 中 | LS 专有，非通用下界 |
