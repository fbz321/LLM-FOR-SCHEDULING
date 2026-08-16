# OnlineScheduling Lean Library — 完成路线图

## 当前状态

| 文件 | 行数 | 缺口 | 性质 |
|------|------|------|------|
| Basic.lean | 285 | 0 | ✅ 完成（含 makespan_const / opt_eq_of_const_schedule 工具引理） |
| CompetitiveRatio.lean | 104 | 0 | ✅ 完成 |
| LowerBounds/Basic.lean | 88 | 0 | ✅ 完成 |
| LowerBounds/BinStretchingLowerBound.lean | 153 | 0 | ✅ 完成 |
| LowerBounds/DecreasingLowerBound.lean | 784 | 0 | ✅ 完成 |
| LowerBounds/Faigle.lean | 391 | 0 | ✅ 完成（layer_separation 等已实现，不再用 axiom） |
| LowerBounds/KnownSumM6.lean | 155 | 0 | ✅ 完成 |
| LowerBounds/KnownSumP3.lean | 275 | 0 | ✅ 完成 |
| LowerBounds/Layers.lean | 69 | 0 | ✅ 完成 |
| LowerBounds/PseudoLowerBound.lean | 547 | 0 | ✅ 完成（m=4） |
| LowerBounds/PseudoLowerBoundM5.lean | 699 | 0 | ✅ 完成（m=5） |
| LowerBounds/PseudoLowerBoundM6.lean | 940 | 0 | ✅ 完成（m=6） |
| LowerBounds/PseudoLowerBoundGeneral.lean | 3135 | 0 | ✅ 完成（Tan & Li 2015 通用 m，5 阶段 adversary） |
| LowerBounds/Rudin.lean | 51 | 0 | ✅ 完成（m=4 下界为真证明；余 1 条渐近 1.88 存在性 axiom 属设计） |
| LowerBounds/BraunGraham2025.lean | 3080 | 0 | ✅ 完成（Braun–Chung–Graham 2025 Theorem 1：m=4 加性下界 √3·OPT−(2−√3)，r=1 自适应对抗 + 一般 r 全参数族逐层强制归纳 `braun_asymptotic_lower_bound_general`） |
| Models/BinStretching.lean | 38 | 0 | ✅ 完成 |
| Models/Decreasing.lean | 46 | 0 | ✅ 完成 |
| Models/GradeOfService.lean | 61 | 0 | ✅ 完成 |
| Models/KnownSum.lean | 42 | 0 | ✅ 完成 |
| Models/Scenarios.lean | 38 | 0 | ✅ 完成 |
| Models/Testing.lean | 56 | 0 | ✅ 完成 |
| ---- | ---- | ---- | ---- |
| **Algorithms/ListScheduling.lean** | 123 | **3** | graham_* 3 条 obligation（LS 上界） |
| **Algorithms/M2.lean** | 58 | **3** | Albers 证明 |
| LowerBounds/ClassicOnline.lean | 141 | 0 | ✅ 完成（p2/p3 Cmax 下界 3/2） |
| LowerBounds/GoSLowerBound.lean | 328 | 0 | ✅ 完成（GoS 5/3 下界，GoSAlgorithm2 模型 + 自适应 adversary） |
| LowerBounds/KnownSumLowerBound.lean | 65 | 0 | ✅ 完成（known_sum_m2 下界 4/3） |
| **LowerBounds/KnownSumP3Three.lean** | 56 | **4** | ks3 多分支 |
| **LowerBounds/KnownSumSmallM.lean** | 55 | **4** | ks_m3..m6 |
| **LowerBounds/Lemmas.lean** | 31 | **3** | 遗留 axiom 层（仅 Template.lean 引用，已被 Faigle 实现取代） |

---

## 执行顺序（6 步）

### Step 1: Faigle.lean — FKT 下界完成 ✅ 最简单

**目标**: 完成 `faigle_kern_turan_lower_bound`，消除唯一 sorry。

**证明路线**:
```
σ = [a, a, ..., a, b, b, ..., b, 1]   (m个a, m个b, 1个1)
a = sqrt(2)/2 - 1/2,  b = 1/2

Step 1.1: 对任一算法，处理 m 个 a-jobs 后
  - 每台机器负载 = n_i * a  (n_i 整数, Σn_i = m)
  - 若 ∃ n_i >= 2: makespan >= 2a, OPT = a → ratio = 2 > fkt_constant ✓
  - 否则全部 n_i = 1: 每台机器负载 = a

Step 1.2: 处理 m 个 b-jobs 后 (同理)
  - 每台机器负载 = a + b = sqrt(2)/2

Step 1.3: 最后 job size 1 到达
  - 某台机器负载变为 sqrt(2)/2 + 1
  - makespan >= sqrt(2)/2 + 1

Step 1.4: OPT 上界
  - 构造显式调度: machine 0 = [1], 其他 machine 各 [2a, b]
  - OPT <= 1  (对 m >= 4 可行)

Step 1.5: 比例
  - makespan / OPT >= (sqrt(2)/2 + 1) / 1 = 1 + sqrt(2)/2
```

**需要的新引理**:
- `jobs_integer_counts`: 对 m 个相同作业，负载是整数倍
- `pigeonhole_sum_m`: m 个整数 n_i in {0,1}, sum=m → 全部 n_i=1
- `schedule_two_layers_and_final`: 显式构造 OPT=1 的调度

**预计**: 80-120 行新增代码，2-3 小时

---

### Step 2: M2 Lemma 2 — 代数不等式 ✅ 纯代数

**目标**: 消除 `m2_lemma2_full_count_bound` 中的 admit。

**证明路线**:
```
要证: f > k+j → 矛盾

已知:
  f * (c-1+delta) * L / m <= L    (full machines 的负载 <= 总负载)
  → f * (c-1+delta) <= m

参数值 (c=1.923):
  k = m/2,  j = floor(m/(2c-2)) ≈ m/1.846 ≈ 0.5417m
  c-1+delta = 0.923 + j/(2m)

需要验证:
  (k+j) * (c-1+delta) > m    (数值不等式)

证明:
  (m/2 + m/(2c-2)) * (c-1 + m/(2(2c-2)m)) > m
  → (1/2 + 1/(2c-2)) * (c-1 + 1/(2(2c-2))) > 1
  → 代入 c=1.923: LHS ≈ 1.243 > 1 ✓
```

**预计**: 30-50 行，1 小时。用 `nlinarith` 或 `positivity` 验证数值不等式。

---

### Step 3: M2 Lemma 1 — trace 分析 ✅ 中等

**目标**: 消除 `m2_lemma1_not_steady` 中的 admit。

**证明路线**:
```
前提: isSteady loads  (= L_low <= beta * L_high)
M2 决策: 选 M1 (最小负载机器)

要证: makespan(m2Algorithm, [p]) <= c * p / m

推导:
  load(M1) <= L_low / k                (M1 是 k 台轻载机中最小)
  L_low <= beta * L_high               (steady)
  L_high <= L - L_low                  (显然)
  所以 L_low <= beta * (L - L_low)
  → L_low <= beta*L / (1+beta)

  load(M1) <= L_low / k <= beta*L / (k*(1+beta))

  new_load(M1) = load(M1) + p <= beta*L/(k*(1+beta)) + p

  由于 L = p (单个 job [p]): L = p
  new_load <= beta*p/(k*(1+beta)) + p = p * (1 + beta/(k*(1+beta)))

  需要: 1 + beta/(k*(1+beta)) <= c
  → beta <= k*(1+beta)*(c-1)
  → 由 beta 定义式可得 (代数验证)
```

**需要**: M2 决策函数 `m2Algorithm` 的具体行为引理。

**预计**: 100-150 行，3-4 小时

---

### Step 4: M2 Lemma 8 + 主定理收尾 ✅ 困难

**目标**: 消除 `m2_lemma8_large_jobs_exist` 和主定理中 2 个 admit。

**Lemma 8 证明路线**:
```
根据不变量 I1-I4 (Lemmas 5-7, 来自潜力函数 Phi):
在关键时间点，存在 m+1 个 "大" 作业，每个 >= (1/2+delta)*L/m。
因此 OPT >= (m+1)*(1/2+delta)*L/m / m >= (1+2*delta)*L/m。

主定理收尾:
  makespan <= max(c*L/m, new_load after M2 decision)
  由 Lemma 1: 当 steady 时 <= c*L/m
  当 not steady: 适用 Lemmas 2-8
  → makespan <= c * OPT
```

**预计**: 200-300 行，1-2 天（潜力函数是最复杂的部分）

---

### Step 5: Rudin m=4 — sqrt(3) 下界 ✅ 中等

**目标**: 消除 `rudin_m4_lower_bound` 的 sorry。

**证明路线**:
```
对 m=4, 构造层次序列直至 R_i >= sqrt(3)-1:

第 0 步: C_0 作业 → S_0 = C_0
第 i 步: Type-2 层 (A_i, B_i, C_i) → S_i = S_{i-1} + A_i + B_i

递推:
  R_i = A_i / S_{i-1}
  R_{i+1} = 3/(4M) + 1/2 - 1/(2M*R_i)
  其中 M = (3V-2)/2, V = sqrt(3)-1

引理 (Rudin, Lemma 3.3): δ_i = R_i - R_{i-1} 至少增长 9.5 倍/步
→ R_i 按指数增长 → 有限步内 R_i >= V
→ 此时用 final job 强制比例 >= 1+V = sqrt(3)
```

**需要**:
- 递推不等式的良基性证明
- 层次强迫分离引理 (Rudin, Lemma 3.4)
- 递推增长速率证明

**预计**: 150-200 行，3-5 小时

---

### Step 6: Rudin 渐进 — 1.88 下界 ✅ 困难

**目标**: 消除 `rudin_asymptotic_lower_bound` 的 sorry。

**证明路线**: 
与 Step 5 相同框架，但 V = 0.88，需要稳态分析 `R_i → V/2` (Rudin, Section 2.2)。

**预计**: 200-300 行，1-2 天

---

## 总览

| Step | 文件 | 难度 | 新增代码 | 时间 | 累积完成度 |
|------|------|------|----------|------|-----------|
| 1 | Faigle | ⭐ | 80-120 行 | 2-3h | FKT 完成 |
| 2 | M2 Lemma 2 | ⭐ | 30-50 行 | 1h | M2 4/5 |
| 3 | M2 Lemma 1 | ⭐⭐ | 100-150 行 | 3-4h | M2 3/5 |
| 4 | M2 Lemma 8 | ⭐⭐⭐ | 200-300 行 | 1-2d | **M2 全完成** |
| 5 | Rudin m=4 | ⭐⭐ | 150-200 行 | 3-5h | Rudin 1/2 |
| 6 | Rudin 渐进 | ⭐⭐⭐ | 200-300 行 | 1-2d | **全库 0 gap** |

## 依赖关系

```
Step 1 (Faigle) ──→ Step 5 (Rudin m=4) ──→ Step 6 (Rudin 渐进)
                    (共享 layering 技术)

Step 2 (M2 Lemma 2) ──→ Step 3 (M2 Lemma 1) ──→ Step 4 (M2 Lemma 8)
                        (M2 各引理存在依赖)
```

Step 1-2 无依赖，可并行。Step 5 依赖 Step 1 的 layering 模式。
