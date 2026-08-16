# Progress Log

## Session 2026-08-15（Theorem 2 r=1 完成：主定理 braun_absolute_lower_bound_1，0 sorry）

### 完成：Braun–Chung–Graham 2025 Theorem 2 的 r=1 实例（绝对竞争比 c₁）全部形式化

- **文件**：`OnlineScheduling/LowerBounds/BraunGraham2025Abs.lean`（1013 行，0 sorry/axiom），
  注册于 `OnlineScheduling.lean`；模块 `lake build OnlineScheduling.LowerBounds.BraunGraham2025Abs` 通过（olean 存在、无 error）。
- **Phase D 收尾（本轮）**，8 个 commit：
  `9a885af`(A defs+cubic) → `ec973bc`(B 根) → `d938e6d`(C 陷阱比) → `73a806d`(Sp1 陷阱+OPT L0/S0/L1)
  → `eea70bf`(L1/S1 slack+有理界) → `3e23190`(S1 打包) → `dda23c5`(Sp1 打包) → `7bd4152`(F 打包)
  → `81c52b2`(base+layer1 强制) → `a4c77eb`(主定理)。
- **本轮新增关键引理**：
  * 可行性/恒等式：`braunAbs_S1_ge_4_4S0`（S1 打包第 4 机，消去后 `−3c²−4c+17≥0`，
    用 c₁<7/4 因式分解）、`braunAbsS0_ge_2`（Sp1 打包，`(3c−5)/(2−c)>0`）、
    `braunAbs_S1_eq_3S0_2L1_2`（F 打包恒等式，对一切 c 成立）、
    `braunAbsS0_pos`/`braunAbsL1_pos`（层分离所需正性）。
  * OPT 打包（上界即可）：`braunAbs_opt_S1_le`（Table 11，15 作业显式分配）、
    `braunAbs_opt_Sp1_le`（Table 10，16 作业）、`braunAbs_opt_F_le`（Table 13，17 作业，
    每机恰 =F，用 `S1=3S0+2L1+2`）。
  * 强制追踪：`braunAbs_base_forcing`（L₀/S₀ 层分离）、`braunAbs_layer1_forcing`
    （L₁/S₁/S⁺₁ 三层 + Sp1 好/坏二分，复用 `braun_layer_separation_from_base`/
    `braun_three_from_base`）。
  * **主定理 `braun_absolute_lower_bound_1 : ∀ alg : OnlineAlgorithm 4, ∃ σ, c₁·OPT σ ≤ makespan alg σ`**。
- **F 打包正确性**（数值核对）：total load = 4F 精确；P1={F}、P2={S⁺₁,S₀,L₁,L₁,L₀,L₀}、
  P3={S₁,S₁}、P4={S₁,S₀×3,L₁×2,L₀×2}，每机 = 2S₁ = F（用 `S₁=3S₀+2L₁+2`）。

### 关键踩坑（本轮，供后续复用）

1. **`native_decide`/`norm_num` 对含自由变量（c、x）的目标报 "free variables"**——Fin 4/Fin 3
   闭式 if 链 + filter.card 的负载计数，改用 `dsimp [scheduleLoads]` + `change (∑ i : Fin n, …)`
   + `rw [Fin.sum_univ_four/three]` + `fin_cases j <;> simp […] <;> ring`（全闭式后再 simp/ring）。
2. **`dsimp only […, l2]` 展开 let 时，let 体里的其它 def 必须在同一 dsimp 列表**——`l2` 体含
   `runAlgorithm (braunAbsBase …)`，漏列 `braunAbsBase` 会导致 let 展开后 `braunAbsBase` 残留在
   RHS、与 LHS 的显式 foldl 链 defeq 不匹配（"step … l2 …" 不归约）。
3. **`nlinarith` 不展开 def**：目标与假设分别经 `dsimp [braunAbsF1]` 后出现
   `l (alg l (2*S1))` vs `l (alg l braunAbsF1)` 两套原子；对策是**别 dsimp**，直接用
   `braunAbsLayerSum1`/`braunAbsF1` 作为原子变量 + `nlinarith [hl]`（hl 用原 def 形式）。
4. **`if_neg` 的证明项要显式 `have hh : … := by …` 再 `exact hij0 hh`**——`;` 链式写法触发
   "No goals to be solved"（rw 已闭合 have 目标后残余目标错位）。

## Session 2026-08-15（Theorem 2 r=1 起步：Phase A/B/C 起手）

> 目标：Braun2025 **Theorem 2（绝对比 √3−ε_r）** 的 r=1 实例。计划见 `task_plan_braun_abs.md`。
> 四个 commit：`9a885af`(A) `ec973bc`(B) `d938e6d`(C起手) `73a806d`(Sp1陷阱+OPT)。全 0 sorry，模块已注册。

- **Phase A**：新文件 `LowerBounds/BraunGraham2025Abs.lean`。参数长度（c 的有理函数）：
  `L0=1`、`S0=(c−1)/(2−c)`、`L1=3/(3c−5)−(c−1)/(2−c)`、`S1=6/(3c−5)+(3−c)/(2−c)`、
  `Sp1=S1+2S0`、`F=2S1`、`LayerSum1=1+S0+L1+S1`、`Seq1`（17 作业）。证
  `braunAbs_cubic`：不动点 c=(Σ+F)/F ⟺ **6c³−28c²+38c−13=0**（paper Table 12 r=1）。
- **Phase B**：`braunAbs_cubic_root_exists`（IVT 于 `isPreconnected_Icc.intermediate_value`，
  取 g=−cubic 使 g(5/3)=−1/3<0<1=g(2)）；`braunAbsCR1`（Classical.choose）；lo/hi/root/
  ne_two/3c5_ne/F_ne（`braunAbsS1_pos`）/`braunAbsCR1_fixedpoint`。**唯一性暂缓**（主定理不需要）。
- **Phase C 起手**：乘法陷阱比 `braunAbs_L0_trap_ratio`（c≤2→c·1≤2）、
  `braunAbs_S0_trap_ratio`（恒等式 c(1+S0)=1+2S0，通用）、`braunAbs_F_trap_ratio`（不动点）、
  `braunAbs_Sp1_trap_ratio`（恒等式 c(Sp1+L1)=Σ+Sp1，通用= L1 的定义方程）；
  OPT witness：`braunAbs_opt_L0/S0/L1`（对角分配，optMakespan_le_of_schedule + ge_avg）。

### 关键发现（sympy 探针 `work/braun_abs_trap_probe.py`）
陷阱比在 c₁ 处：**S0/S⁺₁/F 精确 =c₁（恒等式），L0=2、L1≈1.775、S1≈1.813 松弛 >c₁**。
论文"所有陷阱比都=c"字面不成立，正确表述是紧/松弛两类。

### 关键踩坑（本轮）
- **field_simp 不匹配重排分母**：`3c−5` 与 `−5+c*3` 是 ring 等价但 field_simp 不识别；
  对策：**先 `ring_nf`（目标）再 `ring_nf at h`（假设）统一成 `−5+c*3`**，再 field_simp + ring。
- **松弛陷阱需 c₁ 的有理界**：L1 需 `c₁<7/4`、S1 需 `c₁>12/7`；用
  `cubic(c)−cubic(a)=(c−a)·(二次式)` 因式分解 + 二次式在区间上的符号（nlinarith）证。
- **不等式除正分母**：`mul_le_mul_iff_of_pos_left` 配 `simpa [mul_zero]`（D*0=0 需归一）。

### 剩余（Phase D）
- OPT 打包 witness：`braunAbs_opt_S1_le`（Table 11）、`braunAbs_opt_Sp1`（Table 10）、
  `braunAbs_opt_F`（Table 13）——三个显式 `Fin n → Fin 4` 分配（最难，类比 Theorem 1 `braun_opt_eq_F`）。
- 强制追踪（复用 `braun_layer_separation_from_base`/`braun_three_from_base` 通用计数引理）+ 主定理
  `braun_absolute_lower_bound_1` + 全量 build + 提交。

## Session 2026-08-15（Braun r=1 树回放：认证层完整演示）

### 完成：`braun_tree_r1_lower_bound` —— r=1 实例经 AdvTree.sound 重推（0 sorry）

- 在 `BraunGraham2025Tree.lean` 新增 `BraunTreeR1` 命名空间：把 r=0 的认证层冒烟
  测试推广到 **r=1 主定理实例（17 作业）**——L₀×4 / S₀×4 / L₁×4 / S₁×3 / S⁺₁ / F
  六阶段显式 `AdvTree`，逐叶证书全部机械复用已有引理（层分离 + 陷阱 + OPT 打包）。
- 新增组合子：`place3`/`stage3`/`sum_place3`/`tupleAlg3`/`tupleAlg3_run`（3 作业版）。
- 新增证书：`l1bad`/`s1bad`（层分离陷阱）、`sp1bad`（S⁺₁ 精确陷阱，用
  `braun_prefix_additive_identity`+`braun_opt_prefix_Sp`）、`fgood1`（F 收尾，用
  `braun_additive_identity`+`braun_opt_eq_F`）、`sp1_good_invariant`（S⁺₁ 好路径
  ⇒ ∀i Φ₁≤load_i）、`braunSumLS1_eq`（Φ₁=Φ₀+L₁+S₁）。
- `braunTree1_wellFormed`（内联 `refine`+`by_cases`，同 r=0 套路）、
  `braunTree1_certified`（六阶段嵌套 by_cases + calc 证书）、`braunTree1_rootOK`。
- **验证**：`lake build OnlineScheduling.LowerBounds.BraunGraham2025Tree` 通过
  （8698 jobs），`braun_tree_r1_lower_bound` 为真证明，文件 0 sorry/axiom。

### 关键踩坑（本轮，供后续复用）

1. **`add_le_add_left/right` 方向与直觉相反**（此 mathlib）：`add_le_add_left h c`
   结果是 `a + c ≤ b + c`（c 加在**右**）；要给 `X + a ≤ X + b`（X 加在左）要用
   `add_le_add_right`。直接 `nlinarith` 最省心。
2. **组合子的 WellFormed 不能抽象成独立引理**：`stage4` 等组合子的子节点是
   任意 `leaf` 函数，`(leaf …).sigma/loads` 无法仅凭 `WellFormed(leaf …)` 证明；
   WellFormed 必须**内联**展开，在具体 `.node` 构造处用 `rfl`、在分类器叶处用
   `by_cases <;> simp [leaf, <continuation-stage>, AdvTree.sigma/loads, h]`。
   注意 `<continuation-stage>` 是分类器**续接**的 stage（如 `l1Leaf` 续接 `stage3`），
   不是父 stage。
3. **树见证序列与引理序列的 defeq 对账**：树用 `[] ++ [x,x,x,x]`（字面列表），
   引理用 `List.replicate 4 x`；用 `rw [show (字面) = (replicate 形式) by rfl]`
   对账（左结合 `++` 与 replicate 均 defeq）。
4. **S⁺₁ 好/坏二分**：Sp₁ 落在 j0 ⟺ `∀i Φ₁≤load_i` ⟺ `¬∃j Φ₁+Sp₁≤load_j`；
   分类器用后者（`¬∃` 好分支），`fgood1` 需要的 `∀i Φ₁≤load_i` 由
   `sp1_good_invariant`（S₁ 好 + ¬陷阱 ⇒ m=j0）补出。
5. **F 收尾证书的 loads 参数是 F 之前的状态**：`fgood1 loads hloads mF` 的
   `loads` 是放置 F 之前（= Sp₁ 之后）的负载，不要再包一层 `place … F₁`。

## Session 2026-08-15（BraunGraham2025 一般 r 强制归纳完成：0.2b 收尾）

### 完成：Theorem 1 全参数族（n=8r+9，任意 r）——自适应逐层强制归纳，0 sorry

- **`braun_asymptotic_lower_bound_general`**：∀ r, ∀ alg, ∃ σ 为 σ_r 的前缀
  （`List.IsPrefix σ (braunSeq r)`），makespan ≥ √3·OPT − (2−√3)。对应论文
  Table 3 强制调度的完整归纳；r=1 定理降级为其特例（原语句不变）。
- **逐层不变式**（非均匀）：每层结束后 ∀i, Φ_k ≤ load_i（P4 比其余高 2S_{k−1}）。
  `braun_layerk_forcing_pref`（k≥2）：L_k 层分离陷阱 → S_k 三作业陷阱 →
  S⁺_k 精确陷阱（braun_prefix_additive_identity）或恢复不变式；层 1 用
  `braun_layer1_forcing_pref`（原 layer1_forcing + 前缀证书）；基例
  `braun_base_forcing_pref`。
- **新引理（本轮）**：
  * 非均匀层分离：`braunPlace`（加法形式，局部副本）+ `braun_place4_either` /
    `braun_layer_separation_lb` / `braun_three_from_lb` / `braun_place3_loads_distinct`
    / `braun_four_distinct_univ` / `braun_three_distinct_exists_untouched`
  * 一般 k 陷阱：`braun_trap_Lk`（k≥2，差 = q^{k−1}·(3/α−2) ≤ 0，
    系数经 `braun_SpL_pred_add_mul_alpha`、`braun_trap_Lk_coef` 手工降幂）、
    `braun_trap_Sk`（k≥1，恒等式 (√3−2)S+√3L = L 坍缩为 0 ≤ Φ_{k−1}+(2−√3)）
  * 一般 k 的 OPT witness：`braunLkTrapWitness`/`braunSkTrapWitness` +
    `braun_opt_Lk_trap_le`（k≥2，Table-6 前缀打包 + 对角 L_k）、
    `braun_opt_Sk_trap_le`（k≥1，前缀全塞 M3 + `braun_prefix_total_le_S`：
    totalLoad(前缀) = 3F−c ≤ S_k）
  * 前缀证书：`braun_L0_prefix_pref0`/`braun_prefix_step`/`braun_prefix_mono`/
    `braun_prefix_seq`/`braun_L_witness_prefix`/`braun_S_witness_prefix`/
    `braun_isPrefix_refl`/`braun_isPrefix_trans`
  * `braun_force_general_pref`（r 归纳）+ `step_eq_braunPlace`
- **架构**：base/layer1 forcing 重写为 pref 版本（witness 带 `List.IsPrefix`
  证书），旧名保留为证书剥离的推论；`braun_asymptotic_lower_bound` 由
  general 定理（r=1）重导出。
- 验证：单文件 `lake env lean` EXIT=0、0 sorry；全量 lake build 通过。

### 关键踩坑（本轮，供后续复用）

1. **本工具链 `List.append`（`++`）是左结合**（`append_assoc : (as ++ bs) ++ cs
   = as ++ (bs ++ cs)`）——所有 append 结合性论证按左结合算，calc 的 LHS 必须
   与目标（含未展开 def）逐字一致。
2. **`rfl` 不展开 semireducible def**：`rfl`/`rw` 的自动收尾只在 reducible
   透明层；braunSeq/braunPlace4/braunQ 等 def 出现在目标里必须显式
   `dsimp` 后再 rw/rfl。
3. **`rw [h]` 只重写一次带元变量的模式**：`rw [step_eq_braunPlace]` 对嵌套
   step 链只重写最外层（元变量在首个匹配处固化）；改为
   `simp only [step_eq_braunPlace]` 逐处重写。
4. **`rw` 的副作用目标按生成逆序出现**：`rw [card_insert_of_notMem ×3]` 的
   三个 `∉` 目标顺序是 第3、第2、第1（reverse）；bullet 要按逆序写。
   （本 mathlib 拼写是 `Finset.card_insert_of_notMem`，大写 M。）
5. **`Finset.eq_univ_of_card ?_` 卡住 Fintype 元变量**：必须
   `(s := (…) : Finset (Fin 4))` 显式给出 s。
6. **`Nat.sub_add_cancel hk` 的 a 由 hk 推断**：hk : 2 ≤ k 会生成
   `k − 2 + 2 = k`；要 `k − 1 + 1 = k` 必须传 `(show 1 ≤ k by omega)`。
7. **`mul_le_mul_left` 不是 Iff**（此 mathlib）：0 < a 除不等式用
   `le_of_mul_le_mul_left h a0`。
8. **simp 把等式假设当重写规则**：`simp [h12]`（h12 : m1 = m2）会把整个目标
   的 m1 重写成 m2，毁掉其余 if 条件；陷阱分支改用
   `rw [if_pos h12] + split_ifs`，且 if_neg 的证明必须先 `have` 成
   预类型化项再 rw（否则 rw 拿错误的 if 条件去细化 `by intro h`）。
9. **`fin_cases` 后目标带 `(fun i => i) ⟨0, ⋯⟩`**：rw 不匹配；用
   `change` 归一回 `0` 或改用 nlinarith（defeq 下 nlinarith 不识别，
   必须先 change）。
10. **`Fin.sum_univ_three` 对 `Fin (replicate 3 x).length` 域 rw 失败**：
    先 `change (∑ i : Fin 3, …)`（域 defeq 但 rw 的模式不匹配）。
11. **`subst h`（h : i = m_j）在分支内不可靠**（后续投影报 unknown
    identifier）——不用 subst，直接用 h_j 配 if_pos/if_neg + 显式传递证明。
12. **pwsh `Set-Content -Encoding UTF8` 写入 BOM**，本 Lean 对 BOM 报
    "expected token"——写文件用 `[System.IO.File]::WriteAllText` +
    `UTF8Encoding($false)`。
13. **`rw [show (k−1)+1 = k]` 会重写 binder 变量**（∑ k ∈ range … 里的 k）：
    和式恒等式先把目标形式写成无 binder 冲突的 `show` 再 rw。

## Session 2026-08-15（BraunGraham2025 主定理完成 + 入湖）

### 完成：Theorem 1 全部证明（0 sorry，全量 lake build 8722 jobs 通过）

- **修复上轮遗留的损坏代码**：`scheduleLoads_split_append`（change 目标写反）、
  `braunLayerBlock_makespan_ge`（split 结合性不匹配、if_true/if_false 卫生、
  nlinarith 非线性乘法、`simp only [...] at h` 的依赖动机问题、omega 的
  不透明长度原子）、`braun_opt_prefix_Sp` 的 constructorNameAsVariable linter
  心跳超时（set_option 关闭）。
- **主定理 `braun_asymptotic_lower_bound`**：∀ alg, ∃ σ, makespan ≥ √3·OPT − (2−√3)。
  实现 = 论文 r=1 实例（17 作业）的自适应对抗：
  * 基例：4×L₀ 层分离（陷阱比 2，OPT=L₀）、4×S₀ 层分离（陷阱比 √3，OPT=L₀+S₀）
  * L₁ 陷阱：Φ₀+2L₁ ≥ √3(Φ₀+L₁)−d，witness OPT ≤ Φ₀+L₁（对角打包）
  * S₁ 陷阱：Φ₀+L₁+2S₁ ≥ √3(S₁+L₁)−d，witness OPT ≤ S₁+L₁
    （3 机 {S₁,L₁} + 1 机 {L₁,L₀×4,S₀×4} 的显式分配 braunAssign3S1）
  * S⁺₁ 精确陷阱：braun_prefix_additive_identity 1 + braun_opt_prefix_Sp 1
  * F 收尾：clean 路径 Φ₁+F = √3F−d（braun_additive_identity 1）+ braun_opt_eq_F 1
- **新引理**：braun_sqrt3_le_two、braunα_le_three、braun_trap_L0/S0/L1/S1、
  braun_opt_replicate4_L0、braun_opt_prefix0、braun_opt_prefix_4L1_le、
  braunAssign3S1(+_P0part/_Lpart/_Spart)+braunAssign3S1_loads、
  braun_opt_prefix_3S1_le、braun_three_from_base（3 作业层分离）、
  braun_base_forcing、braun_layer1_forcing。
- **入湖**：文件移入 `OnlineScheduling/OnlineScheduling/LowerBounds/BraunGraham2025.lean`，
  注册 `OnlineScheduling.LowerBounds.BraunGraham2025`；全量 lake build 通过。
- **文档同步**：README、ROADMAP、THEOREMS_ARCHIVE、RESEARCH_PLAN（0.2 完成 +
  0.2b 一般 r 归纳留作可选扩展）、LOWER_BOUND_TODOLIST（第 12 个自适应定理）、
  braun_router.py（SUBGOALS 清空，标记全部完成）、braun_verifier.py 路径更新。

### 关键踩坑（本轮，供后续复用）

1. **Fin 域 ≠ 语法域**：`(List.replicate 4 x).length` 与 `4` 是 defeq，但
   `Fin.sum_univ_four` 的 rw 对"def 应用 + 域为 Fin (replicate…).length"的
   filter 谓词不匹配（pattern ∑ i, ?f i 找不到）——把辅助 assign 的域直接写
   `Fin 4`/`Fin 3` 即解决。
2. **Real.sqrt 是 noncomputable**：任何 val 中出现 `List.replicate 4 (braunL 1)`
   这类含 √3 的项 → 依赖非计算 → `native_decide` 编译失败。对策：Fin val 用
   纯 Nat 算术（12 + i.1 而不是 8 + (replicate 4 …).length + i.1）。
   native_decide 对"闭式 Fin 4 链式 if + filter.card"计数非常好用（dsimp 后）。
3. **rw 对嵌套 Fin 投影不匹配**：h2 split 的 assign 组合产生 `a ⟨↑⟨↑i, ⋯⟩, ⋯⟩`，
   count 引理 rw 失败；对策：rw [h1, h2] 后用 `change` 把三个 summand 的
   assign 规范化成带显式 `(i : Fin 4)/(i : Fin 3)/(i : Fin 1)` 注解的 lambda，
   再 rw（binder 注解必须与 change 目标一致）。
4. **nlinarith 不会乘不等式**：cL ≥ 1 与 L ≥ 0 推不出 cL·L ≥ L；需显式
   `mul_le_mul_of_nonneg_right`。同理 nlinarith 不会在乘积里替换 cS = 1，
   需显式 `(cS : ℝ) * S = S`。
5. **`simp [h] at * ⊢` 是语法错误**（此版 Lean）：用 `simp [h] at *`（`at *`
   已含目标）。`simp [h, h.symm]` 会 maxRecDepth 死循环；if 翻转用
   `rw [if_pos h, if_pos h.symm]`。
6. **rw 在依赖类型的假设上失败**（motive is not type correct）：假设 h 的类型
   经局部变量 i 的 Fin 域引用被改写的长度 → 先 `have hi7 : i.1 < 7 := by omega`
   （omega 用等式原子），再 rw 目标。
7. **omega 看不到 List.length/replicate 的不透明原子**：Fin 界证明先 `have h4 :
   (replicate 4 x).length = 4 := by simp` 再 omega。
8. **`let` 与 rw**：`by_cases h : j = j0`（j 是 let 绑定）后 `rw [h]` 不匹配——
   直接用 `alg l2 (braunSp 1)` 显式写，不用 let。
9. **dsimp 不展开 Finset.range 求和**：braunSumLS 1 的化简要
   `simp [braunSumLS, Finset.sum_range_succ]`（dsimp only 只展开 def）。
10. **simpa 过度化简**：hbad2 类"foldl 形式 vs runAlgorithm 形式"的 defeq 目标
    用 `exact`（simpa 会把一边的 foldl 展开成 step 链造成 mismatch）。

## Session 2026-08-14（续 8：Braun 2025 补完接到 flash→pro 自适应路由）

- 用户澄清：`bottleneck_reflection/run_router.py` 的**自适应路由机制（flash 先试 → Lean 验证失败 → 升级 pro）是对的**，目标不该是 1.89 搜索（Faigle 结构到不了），而应接到**上一个任务**——补完 `BraunGraham2025.lean`。
- 新增 Braun 专用件（都在 `bottleneck_reflection/`）：
  * `braun_verifier.py`：`BraunVerifier` 把 LLM 片段插入 `BraunGraham2025.lean` 副本（`end` 之前）单文件编译，复用 `LeanResult`。
  * `prompts/braun_system.txt`：v2 `optMakespan` 基础 + 可用引理清单 + 战术坑。
  * `prompts/braun_task.txt`：单声明任务模板。
  * `braun_router.py`：`SUBGOALS` 列表（`braun_opt_prefix_Sp`、`braun_asymptotic_lower_bound`），每子目标 flash→pro + 修复循环；`--no-api` 干跑。
- 修了两个真 bug：
  * `lean_verifier._parse_errors` 之前把 `warning:` 也当 error 计数（把文件里既有 warning 误报成 error，污染给 LLM 的错误摘要）→ 只匹配 `error:`。
  * `subprocess.run(text=True)` 在 Windows GBK 下解 lean 输出报 `UnicodeDecodeError`（stderr=None）→ 加 `encoding="utf-8", errors="replace"`。
- 给 `BraunGraham2025.lean` 加了 `braunPrefixSp k`（前缀定义，供 LLM 引用），文件仍 0 sorry 编译通过。
- 离线冒烟全绿：`braun_verifier.py`（Compiles:True）、`braun_router.py --no-api`、`test_model_router.py`、`test_llm_client.py`。
- 运行（需 API key）：`python braun_router.py`（读 `DEEPSEEK_API_KEY` 或项目根 `.env`）。成功片段写到 `experiments/<run>/fragments.txt`、合并结果 `BraunGraham2025.merged.lean`。

## Session 2026-08-14（续 6：BraunGraham2025 组装收尾——OPT = F 完成）

### 完成：4 个机器 sorry 全部填平 + OPT = F（单文件编译通过，0 sorry）

- 新增机器负载引理（都放在文件末尾，因依赖 `braun_M1_eq_F`/`braun_total_work`/
  `braun_opt_ge_F` 等后置声明）：
  * `braun_load_M0_eq_F`：M0 = F（L0/S0/blocks 段贡献 0，F 段 = F）
  * `braun_load_M1_eq_F`：M1 = Σ(2L_k+S⁺_k) + 2S₀ = F（`braun_M1_eq_F` + 和项换序）
  * `braun_load_M2_eq_F`（需 `1 ≤ r`）：blocks 顶层给 M2 两个 S_r = F
    —— **求和索引论证**：`∑ t∈range r (if t+1=r then 2S_{t+1} else 0)` 用
    `Finset.sum_eq_single_of_mem (r-1)` 坍缩（只有 t+1=r 非零）
  * `braun_load_M3_lt_F`（需 `1 ≤ r`）：`f 3 = ∑f − f0 − f1 − f2`（`Fin.sum_univ_four`
    提取）+ `sum_scheduleLoads` + M0/M1/M2=F + `braun_total_work` → F − c < F
- **发现并修复 r=0 边界 bug**：原 `braunAssign` 对 r=0 把 S₀ 2 个给 M1、2 个给 M3，
  但 r=0 无顶层 S_r block → M2 空、M3=4+2α > F=2α，打包失效。
  修复：`braunAssign0`（S₀ 改 2 个给 M1、2 个给 M2）+ `braun_opt_le_F` 按 r=0 / r≥1 分情况。
- `braun_opt_le_F`（重写，r=0 用 braunAssign0、r≥1 用 braunAssign）+ `braun_opt_ge_F`
  → **`braun_opt_eq_F`：optMakespan (m:=4) (braunSeq r) = braunF r**。
- 文件编译通过（`lake env lean BraunGraham2025.lean`，EXIT=0，**0 sorry**）。

### 关键踩坑（本轮，供后续复用）

1. `Fin.sum_univ_four` 在本 mathlib 版本**存在**（由 `prod_univ_four` 的 `to_additive`
   生成）——之前 progress 记的"不存在"是旧版本结论。
2. `Finset.sum_eq_single` 第二显式参数是 `a ∉ s → f a = 0`（不是 `a ∈ s`）；
   要"a ∈ s"版本用 **`Finset.sum_eq_single_of_mem a hmem h₀`**。
3. `omega` 在本文件对含 `r - 1` 的 Nat 目标报 "metavariable" 错误；
   改用 `Nat.add_sub_cancel`（b+1=r → b=r−1）和 `Nat.sub_lt`（r−1<r）避免。
4. `decide` 不能处理含自由变量的 `if i.1 < 2 then ...` 目标；对 Fin 4 上的分配函数，
   用 `fin_cases i <;> decide` 消元后再判。
5. `rw [引理 0]` 匹配 `scheduleLoads ... 0` 会因 `fin_cases j` 后目标出现
   `(fun i => i) ⟨0,⋯⟩` 而失败；改用 `exact le_of_eq (引理)`（`exact` 走 defeq 一致）。
6. 机器 0 负载 0 类子目标：`unfold assign; fin_cases i <;> decide`（或常量分配直接
   `decide`）；用 `scheduleLoads_zero_of_forall_ne` 统一封装。
7. `lean-check.ps1` 已重建（原脚本不在仓库）：`lake env lean <file>` 单文件编译。

### 下一步（强制调度 + 主定理）

- **重要修正**：固定序列版 `algorithmMakespan 4 alg (braunSeq r) ≥ braunForcedMakespan r`
  **不成立**——存在在线算法（"猜" Table 7 打包）在 σ_r 上直接达到 OPT=F。
  正确表述是**自适应对抗**：`∀ alg, ∃ σ, algorithmMakespan 4 alg σ ≥ √3·τ_o(σ) − (2−√3)`，
  对抗者观察 alg 的放置逐步释放作业，一旦偏离"整齐"调度即以短前缀终止。
- 需要：层分离引理（v2，无 OPT）、前缀 OPT（Table 6：OPT(S⁺_k 前缀) = S⁺_k + L_k）、
  前缀加性恒等式（Σ(L+S)+S⁺_k = √3(S⁺_k+L_k) − (2−√3)）、
  最终 F 的强制（clean 路径 makespan = braunForcedMakespan = √3F − (2−√3)）。

## Session 2026-08-14（续 7：强制调度基础——层分离 + 前缀加性恒等式）

### 完成（单文件编译通过，0 sorry）

- **`braun_layer_separation_from_base`**（v2，无 OPT，从 Faigle 适配到 m=4）：
  均匀 base 上 4 个相同作业 x，要么 makespan ≥ base+2x，要么 4 机全部 = base+x。
  （依赖 `braun_loads_multiples_from_base` 倍数保持 + `pigeonhole_all_ones`）
- **`braun_prefix_additive_identity`**（S⁺_k 偏离陷阱，k≥1）：
  `braunSumLS k + braunSp k = √3·(braunSp k + braunL k) − (2−√3)`，
  即 Φ_k + S⁺_k = √3·τ_o(S⁺_k 前缀) − d（把 S⁺_k 放错机器时的强制比）。
  —— 系数恒等式 hc0=(1+α)/(q−1)=3−α、hc1 通过 α²→2α+2 逐次降幂（hα2..hα6）证明。

### 关键踩坑（续 7）

1. **`polyrith` 已下线**（"external service shut down"），多项式恒等式改用手工降幂：
   `hα2..hα6`（α^n 的线性闭式）由 `braun_poly2` 递推算出，`ring_nf` 后 `nlinarith [hα2..hα6]`。
2. **`rw [hk']`（k=(k−1)+1）会改写 `k−1` 内的 `k`** → `k−1+1−1` 残渣；
   只改指数用 `conv_lhs => rw [← Nat.sub_add_cancel hk]`。
3. `pow_succ`（右递归 `a^(n+1)=a^n*a`）vs `pow_succ'`（左递归 `a^(n+1)=a*a^n`）方向易混。
4. `simp_rw` 在 `ring_nf` 之后会因 pow 已展开成乘积而 "no progress"；降幂要在 ring_nf 前
   或改用 `nlinarith`（monomial 归一化）收尾。

### 剩余（主定理组装，未完成）

- `braun_opt_prefix_Sp k`（Table 6 打包）：OPT(L₀,S₀, blocks 1..k) = S⁺_k + L_k —— 与
  `braun_opt_le_F` 同型的显式分配 + sup'_le 组装（约 100+ 行）。
- 自适应对抗归纳：L₀/S₀ 基例（层分离判 2 或 √3 比）→ 每层 L_k 强制分散 → S⁺_k 偏离即 STOP
  （用 `braun_prefix_additive_identity` + `braun_opt_prefix_Sp`）→ 最终 F（clean 路径
  `braun_additive_identity` 得 √3F−d）。
- 主定理 `∀ alg, ∃ σ, algorithmMakespan 4 alg σ ≥ √3·optMakespan (m:=4) σ − (2−√3)`。

## Session 2026-08-14（线 A：k=3 尺寸优化搜索重启）

### 背景回顾

- 昨天 08-13 深夜启动 `adversary_search/pattern_opt.py` 的 k=3 优化（k3_run.log 只有
  workers 覆盖 updating 的 warning，无任何输出即被中断）——原因已查明：
  **scipy `differential_evolution` 在 `workers>1` 时禁用 callback**，且 `updating='immediate'`
  被覆盖为 'deferred'，导致每代进度不打印；单次 k=3 eval 需 60–100s（4 尺寸 × 深度 13），
  完整 DE（popsize 8 × 15 代 = 480 eval）单线程要十几小时，被中断后无任何留档。

### 本次修复与改动（pattern_opt.py）

- `_objective` 增加文件日志（evals.log，含 PID/序号/尺寸/值，worker 并行时也可留档）
- `optimize()` 主 DE 阶段支持 `--target` 可达性封顶（≈√3 时快速剪枝返回）
- main 增加 `--target` 参数；`--no-polish` 可跳过 Nelder-Mead 精修（单次 eval 太贵）
- 冒烟测试通过：FKT 尺寸 (0.2071,0.5,1.0) → 1.707 ✓、(0.25,0.5,1.0) → 5/3 ✓
- k=2 迷你 DE（maxiter=3, popsize=4）23s 跑通，管线完整

### 进行中

- k=3 搜索后台运行中：`--k 3 --maxiter 10 --popsize 6 --workers 8 --target 1.73206 --no-polish`
  （≈240 eval × 60–100s / 8 workers ≈ 1–1.5h），结果待收集

### 结果（已完成，2026-08-14 下午）

**k=3 搜索完成（负结果，有价值）**：4 尺寸 × 深度 13，DE（popsize 6 × 10 代，≈420 eval，
4 workers，9568.7s ≈ 2.7h）最优值 **1.7020**（尺寸 [1.3556, 0.2647, 0.6763, 0.2757]，
整数 (10⁶, 195278, 498894, 203360)），**未突破 √3≈1.73205**。

- 对抗路径揭示最优结构 = 类 FKT 两层：4×203360（分散）+ 3×498894（分散）+
  1×1000000（打爆一台）→ makespan 1702254 / OPT 1000000 = 1.7023。
- 结论：尺寸数 ≤4、深度 ≤13 的构造类天花板约 1.702（甚至低于 FKT 1.707），
  突破 √3 需要更多尺寸/更深（Rudin √3 用 33 作业、10+ 尺寸）；
  下一步：k=4（5 尺寸 × 17 深）需先优化搜索器（alpha-beta/支配剪枝），
  或转"层结构约束 + 尺寸优化"（RESULTS.md 结论 3）。
- 已记录：RESULTS.md（v2 节）、findings.md（工程坑：workers callback 禁用、
  Python PATH stub 9009、缓存上限导致 LRU 淘汰风暴 100s→600s+、Python 分配器
  不返还 OS 内存 → cache_clear+gc+限制并发）、progress.md（本节）。

### 本轮工程修复汇总

1. **scipy workers 坑**：workers>1 禁用 callback → 进度改文件日志（evals.log）
2. **PATH stub 坑**：`python` 解析到 WindowsApps stub（exit 9009）→ 用绝对路径
   `D:\Anaconda3\python.exe`
3. **内存爆炸**：opt 全局缓存 200k 上限（跨 eval 累积）+ value 缓存必须
   maxsize=None（设上限触发 LRU 淘汰风暴，95s→>600s）+ eval 后
   cache_clear+gc.collect + workers 8→4 → 内存稳定 ~4GB 内

### 续：Braun2025 机制探针（同日）

- 用户提问"为什么 AI 能提模板 / 为什么 Braun2025 构造正确"，用 Lean 复现回答：
- 新增 `OnlineScheduling/BraunKey.lean`（独立探针，只 import Mathlib，
  **24s 单文件编译通过，不触发全库 lake build**——快速复现方式的样板）
- 复现机制核心（全部 Lean 验证）：
  * `α_unique`：α²−2α−2=0 正根唯一 = 1+√3（"为什么尺寸比只能是 α"）
  * `ratio_decomp`：τ_A/τ_o = 1 + α(1+α)/(q−1) − 余项(r)（机制心脏）
  * `ratio_limit`：1 + α(1+α)/(q−1) = √3（代数坍缩，非近似是恒等式）
  * `additive_coeff` / `forced_makespan_additive`：d=2−√3 精确、加性恒等式逐 r 成立
- 结论记录在 findings.md：
  * Braun 正确 = 强制调度唯一 + 逃生路径比值可算 + 代数坍缩（α 极小多项式）
  * AI 能提模板 = 层模式组合（LLM 见过文献结构）+ 数值验证兜底 +
    Lean 证代数；分工 = LLM 提结构/优化器找尺寸/Lean 证代数
- 快速复现方式（避免全库编译）：只 import Mathlib 的独立文件 +
  lean-check.ps1 单文件编译（24s vs 全库 10+ 分钟）

### 续 2：BraunGraham2025.lean 打包不变量（同日）

- 新增 5 个引理/定理（单文件编译通过，24s）：
  `braunLayerBlock_sum` / `braunBlocks_sum` / `braunSeq_sum_decomp` /
  **`braun_totalLoad_eq`**（totalLoad = 4ΣL + 6ΣS）/
  **`braun_total_work`**（totalLoad = 4F − (4+6α)/(q−1)，常数亏损 ≈1.464 与 r 无关）
- 数值验证 Table 7 递归打包的容量恒等式：**6α(q−1) = (4+4α+1/α)·q 精确成立**
  （差 = 0.000000，由 α²−2α−2=0 导出）——顶层作业总量恰好 = 3 台容量增量，无 slack，
  解释为什么打包必须几乎满载（P1={F}、P4={S_r,S_r} 满载）。
- 下一步：完整 Table 7 打包（递归分配 → OPT ≤ F → 与 braun_opt_ge_F 合得 OPT = F），
  再强制调度归纳（Table 3）、主定理。详见 findings.md。

### 续 5：decomp 引理完成 + 组装收尾（同日）

- **`braunAssign_loads_decomp` 真证明完成**（非 sorry）：
  `scheduleLoads σ braunAssign j = L₀段 + S₀段 + blocks段 + F段`
  —— 关键重构：`braunAssign` 域直接设为 `Fin (braunSeq r).length`（内部类型转换），
  消除 a' 中转，`change` + 三次 `scheduleLoads_append` + ring 闭合。
- `braun_opt_le_F` 框架完整：`optMakespan_le_of_schedule` + `sup'_le` + `hdec` 分解。
- **剩 4 个 sorry**（4 台机器负载 ≤ F 的组装收尾）：
  - 机器 0：L₀/S₀/blocks 不给 M0，F 段 = F（简单，simp+omega 半自动）
  - 机器 1：L₀段0+S₀段2S₀+blocks段Σ(2L+S⁺)+F段0 = F（braun_M1_eq_F）
  - 机器 2：blocks 顶层 2S_r = F（需对 t∈range r 求和，仅 t+1=r 非零）
  - 机器 3：< F（braun_M3_lt_F）
- 文件 737 行，编译通过（24s，含 4 个标注 sorry）。
- 踩坑记录：scheduleLoads 的 if 求值（`(fun i => i) ⟨0,⋯⟩` 需 simp 归一）、
  `rw` 改写 braunSeq 会破坏 braunAssign 类型（motive 错误）→ 用 change 统一、
  `Fin.sum_univ_four` 不存在、`braunBlocksAssign_loads` 需显式 j 参数。
- 下一步（纯机械）：逐台填 4 个 sorry（机器 0 最易、机器 2 需求和索引论证），
  然后 `braun_opt_le_F` + `braun_opt_ge_F` → **OPT = F**。

### 续 4：显式分配框架（同日）

- 新增：`braunBlockAssign`（block 内 8 位置 → 4 机）、`braunL0Assign`/`braunS0Assign`/
  `braunFAssign`、`braunBlocksAssign`（blocks 递归分配，用 appendAssign）、
  `braunAssign`（σ_r 完整分配，嵌套 appendAssign）、`braunSeq_eq_decomp`
- 验证：`braunBlockAssign_loads`（M1=2L+S⁺、M2=2S(顶层)、M3=其余）、
  `braunS0Assign_loads`/`braunL0Assign_loads`/`braunFAssign_loads`、
  `braunBlocksAssign_loads`（递归负载 = 各 block 负载和）
- `braun_opt_le_F` 框架就位（`optMakespan_le_of_schedule` + `sup'_le` + 类型转换 a'），
  **剩 4 个 sorry**（每台负载 ≤ F 的机械组装：嵌套 scheduleLoads 展开 +
  负载恒等式组合）。文件 649 行，编译通过（24s，含 sorry）。
- 剩余组装（纯机械，无新数学）：机器 0（simp 已自动闭）、机器 1（M1=F 恒等式）、
  机器 2（2S_r=F）、机器 3（M3<F 恒等式）。

### 续 3：Table 7 打包恒等式全部机器验证（同日）

- 新增：`braun_geom_sum_lt`（Σ_{k<r}q^k 闭式）、**`braun_M1_eq_F`**、
  **`braun_M3_lt_F`**（单文件编译通过，24s）
- **Table 7 四机负载全确定**（数值 + Lean）：
  | 机器 | 内容 | 负载 |
  |---|---|---|
  | M0 | {F} | F |
  | M1 | Σ_{k=1..r}(S⁺_k+2L_k)+2S₀ | **F**（`braun_M1_eq_F`，系数 [(α+2)q+2α]=2α(q−1) 坍缩） |
  | M2 | {S_r, S_r} | F（2S_r=F 定义） |
  | M3 | 剩余全部 | **F − (4+6α)/(q−1) < F**（`braun_M3_lt_F`，由 total_work+M1 推出） |
- M3 是唯一有 slack 的机器（slack = 常数 1.464，与 r 无关）。
- 剩余：显式分配函数（σ_r → 4 机）→ `optMakespan_le_of_schedule` 得 OPT ≤ F，
  与 braun_opt_ge_F 合得 **OPT = F**——纯组合构造，无新数学。

## Session 2026-08-08（Braun2025 研究启动）

### 完成

- 研究调研：m=4 上界确认为 26/15（Chen et al. 1994），Braun–Chung–Graham 2025
  加性下界 √3·OPT−(2−√3) 仍未突破 √3；写下 RESEARCH_PLAN.md（A/B/C/D 四线）
- 下载 12 篇论文入 papers/_inbox（含 HAL Anubis PoW 自动通过脚本），list.csv 更新至 39 条
- Braun2025 数值仿真全通过：OPT=F、加性恒等式精确、前缀 OPT = S⁺_k+L_k
- `OnlineScheduling/BraunGraham2025.lean`：定义层 + 全部代数恒等式编译通过
  （0 sorry；braun_additive_identity 精确加性恒等式；未注册入构建）


### 续：OPT 公理不一致 —— 发现并修复（同日）

- 准备证 Table 7 打包时发现 `opt_le_of_schedule` 签名缺陷 → ProbeOPT.lean 证明
  旧公理集推出 False（OPT 坍缩为平均负载，与最大作业界矛盾）
- Basic.lean 新增 v2 可靠基础：`scheduleLoads` + `optMakespan`（分配上的具体最小值）
  + 5 个定理（le_schedule / le_of_schedule / ge_max_job / ge_avg / nonneg），编译通过
- BraunGraham2025.lean 迁移到新基础，编译通过（braun_opt_ge_F）
- 旧公理隔离（WARNING 注释），24 个遗留文件待迁移（清单见 findings.md）
- Table 7 打包证明顺延（依赖的正是新基础的 opt_le_of_schedule）

### 续 2：v2 基础完成 + 全库验证（2026-08-10）

- Basic.lean 打包机器就绪：`appendAssign`/`scheduleLoads_cons`/`scheduleLoads_append`
  （拼接序列负载 = 两半之和，归纳证明）、`diagAssignReplicate`/
  `scheduleLoads_replicate_diag`（replicate 对角分配每机恰一作业）
- 踩坑汇总（供 skill pitfalls 参考）：
  * Fin 结构 Prop 字段定义级证明无关：⟨v,p⟩ 与 ⟨v,q⟩ defeq，大量 Fin 相等步骤自动闭合
  * ite/dite 条件上的 rw 有 motive 问题 → 用 simp/if_pos/if_neg/split
  * `length ((p::σ)++τ)` 形式没有 OfNat (Fin ·) 0 实例 → 用显式 ⟨0, by simp⟩ 或
    类型标注 (0 : Fin (p :: (σ++τ)).length)
  * rw 匹配 ⟨0, by simp⟩ vs 字面 0 失败时，把引理陈述写成与目标同构的字面形式
  * Nat.sub 化简：(k+1)−(σ.length+1) 不定义归约，用 Nat.add_sub_add_right
- `maxJobSize_le_of_forall` 与 PseudoLowerBoundGeneral 同名 private 引理冲突
  → Basic 版本改 private 解决
- 全库逐模块串行构建通过（Scenarios 一次 I/O 抖动重试通过；并行构建在 G: 盘上
  持续随机 "failed to read file"——该盘读并发不稳，构建一律用串行/单线程）
### 下一步

- Braun2025 形式化：强制调度归纳（Table 3）→ OPT 打包（Table 7，残差不变式）→ 主定理
- 然后按 RESEARCH_PLAN Phase 0：graham_tightness、归档更新


## Session 2026-08-06（Rudin 构造修复 + 打包层，进行中）

### 重大发现：终止层缺夹逼（数学 bug）

- 数值扫描确认：当前已提交的 raw `rudinStep` 在 ε≈2e-5 时 rawR_n≈1.013>1，
  B_n<0（负作业），构造被缺陷算法击穿（最终比率 < 1+V）
- 论文原文 `R_i = max(1, A_i/S_i)` 印刷与逻辑矛盾；正确语义 = 终止层夹逼
  `A_n := min(A_n, S_n), B_n := S_n − A_n`
- 顶层下一层（n−1）的 B 行违规与 A4 违规需要**更紧的 OPT 界**：
  `OPT ≤ S_n + B_{n−1}`（顶层打包）与 `OPT ≤ A_{n−1}+B_{n−1}+2·AC_n`
  （Lemma 3.3 结构打包，需 2·BC_n ≤ AC_n）
- 已实现：双序列方案（raw 分析不动 + 夹逼构造 AC/BC），
  `rudin_packing_C`、`rudin_opt_le_B_violation_C`、`rudin_opt_le_A23`、
  `rudin_opt_le_top_B`、`rudin_opt_le_top_A4`、几何衰减（A_{i+1} ≤ A_i/4）、
  `rudin_totalLoad_C_le` 全部编译通过（单文件 lake build OK）

### 当前状态

- Rudin.lean 单文件编译通过；剩余：比率引理（B/A23/A4 三路 + 顶层）、
  运行追踪归纳（Layer separation）、Lemma 3.5、主定理替换 axiom
- 坑记录：`j+1` 与 `j.succ` 在 rw/simp 中不互相匹配（用 omega 出的
  `hz1 : j+1 = N` 显式重写）；`1+(n−1)` vs `(n−1)+1` 显示一致但模式不同；
  field_simp 需要显式 `3V−2 ≠ 0`；nlinarith 不展开 let（需 dsimp）

## Session 2026-08-06（续 2）：分层追踪实现

### 已完成（全部编译通过，单文件 lake build OK）

- 行处理机制：`runAlgorithm_append_replicate_counts`（n 个相同作业的计数）、
  `rudin_row_dichotomy_4`/`_3`（碰撞/分散二分）、`runAlgorithm_zero_prefix`
- 比率引理：`rudin_B_ratio_lb`、`rudin_top_B_ratio_ge`、`rudin_A23_ratio_ge_C`、
  `rudin_A4_ratio_ge_C`、`rudin_top_A4_ratio_ge`、`rudin_fV_mul_4M`、
  `rudin_fV_bound`、`rudin_rawR_le_fV`、`rudinR_le_one_over_fourM`、
  `rudinA_succ_le_quarter`、`rudinS_le_two_AC`、`rudinS_le_B_pred`、
  `rudin_two_BC_le_AC`、`rudin_totalLoad_C_le`、`rudinS_eq_add_of_lt`
- OPT 打包：`rudin_opt_le_full_B_row_C`、`rudin_opt_le_A3`、
  `rudin_opt_le_top_B`（改 4 个 B）、`rudin_opt_le_top_A4`（Lemma 3.3 结构）、
  `rudin_opt_le_layer_n`、`rudin_B_violation_ratio_C`、
  `rudin_top_B_violation_ratio`、`rudin_top_A_collision_ratio`
- 顶层基例 `rudin_base_layer_n`（BC_n>0 / =0 分叉，B 行碰撞比率 2、
  A 行碰撞比率 1+R_n、全分散 = S_n）—— 编译通过

### 关键发现：序列顺序问题

- 已提交的 `rudinPrefixJobsC` 按 layer 0 在前构造（prefix(i) = layer(i) ++ prefix(i+1)），
  与论文相反（论文 layer n 在前）。OPT 界不受顺序影响（multiset），
  但运行追踪的"前缀违规"论证需要论文顺序
- 计划：新增 `rudinPrefixJobsR`（论文顺序：prefixR(i) = prefixR(i+1) ++ layer(i)），
  追踪用 R 版本；OPT 界通过 `rudin_totalLoad_R_eq_C` 复用 C 版本打包

### 剩余（下一步）

- `rudin_layer_step_R`：B 行碰撞（两路：i≤n−2 用 `rudin_B_violation_ratio_C`，
  i=n−1 用 `rudin_top_B_violation_ratio`）、A 行 3 作业碰撞（`rudin_opt_le_A3_R` +
  `rudin_A23_ratio_ge_C`）、大作业碰撞（A4：`rudin_opt_le_full_layer_R` /
  `rudin_opt_le_top_A4_R` + `rudin_A4_ratio_ge_C` / `rudin_top_A4_ratio_ge`）、
  大作业到空机器（分裂不变式 S_{i+1}+B+A = S_i，需计数论证唯一无 A 机器）
- `rudin_layer_separation`（下降归纳）、`rudin_final_job_forces`（Lemma 3.5：
  终作业 2A_0，OPT ≤ 2A_0 三组打包 + 终作业）、
  `rudin_m4_adversary_exists` 替换 axiom（ε' = min(ε, 1/100) 归约）、
  `rudin_m4_lower_bound`
- 片段文件（TrackingFragment.lean）含未完成草稿，已删除；下一步从
  `rudinPrefixJobsR` 定义与 `rudin_opt_le_full_layer_R` 开始重写

## Session 2026-08-06

- 找到 Park-Chang-Lee 2006 原文：`papers/_inbox` 原本没有该 PDF（list.csv 第 26 行
  只登记未入库）；通过 sci-hub.ru 下载全文并存入
  `papers/_inbox/ParkChang2006-online-semi-online-GoS.pdf`（5 页，DOI 10.1016/j.orl.2005.11.004）
- 重写 `GoSLowerBound.lean`：
  - 删除错误的 axiom `gos_online_lower_bound_five_thirds_proof_obligation`
    （原陈述对普通 `OnlineAlgorithm 2` 的析取式不成立——LS 就能同时打爆三个分支）
  - 新增 GoS 约束模型：`GoSAlgorithm2`（`choose` + `respects`，机器 0 收全部、
    机器 1 只收 g=two）、`gosStep` / `gosRunAlgorithm` / `gosAlgorithmMakespan`
  - 按论文 Lemma 1 完成 5/3 自适应 adversary：
    - 分支 A（`[1,1]` 同机，ratio 2）复用 `Faigle.layer_separation`
    - 分支 B1/B2a/B2b 用逐步步进引理 `gos_step_load` / `gos_step_load_other` 算负载
    - 主定理 `gos_online_lower_bound_five_thirds : ∀ alg : GoSAlgorithm2, ∃ gs, makespan ≥ 5/3·OPT`
  - 四个 OPT 值引理保留（gos_opt_A/B1/B2a/B2b）
- 注册 `import OnlineScheduling.LowerBounds.GoSLowerBound` 到 `OnlineScheduling.lean`
- 验证：单文件编译 OK + 全量 `lake build` EXIT=0
- 文档同步：`THEOREMS_ARCHIVE.md`（156/167）、`ROADMAP.md`、`LOWER_BOUND_TODOLIST.md`
- 待提交：本次 GoS 主定理 + 上轮未提交的 ClassicOnline 重写、GoS 四条 OPT、KnownSumLowerBound

## Session 2026-08-06（查重/引理抽取）

- 全库 Lean 声明盘点：30 个 .lean 文件、约 250 个声明，脚本按声明名查重
- 新增通用引理（`Basic.lean`）：
  - `makespan_const c`：常量负载向量的 makespan = c（`Finset.sup'_const`）
  - `opt_eq_of_const_schedule σ c (h : totalLoad σ = m·c)`：常量调度 ⇒ OPT = c
- 用新引理消除重复证明（公共签名不变）：
  - `ClassicOnline`：`opt_two_ones`/`opt_three_ones` 改用 `Faigle.opt_of_identical_jobs`；
    `opt_two_ones_two` 改用 `opt_eq_of_const_schedule`
  - `GoSLowerBound`：`gos_opt_A/B1/B2a/B2b` 四条 20+ 行 le_antisymm → 各 2 行
  - `KnownSumLowerBound`：`ks2_case1_opt`/`ks2_case2_opt` 同
  - `KnownSumP3`：定理内联的 `h_opt1`/`h_opt2`（与 KnownSumLowerBound 私有引理重复）同
  - `DecreasingLowerBound`：`h_opt_three`/`h_opt_six` 同
- 全量 `lake build` EXIT=0；文档计数更新（THEOREMS_ARCHIVE 169/158、ROADMAP 行数）
- 发现但未动的重复（报告用）：
  - `LowerBounds/Lemmas.lean` 3 条 axiom（opt_of_identical_jobs / layer_separation /
    layer_separation_from_base）与 `Faigle.lean` 已证引理同名重复——遗留层，
    仅 `Template.lean` 与 `bottleneck_reflection/templates` 引用，不在构建索引，保留
  - `PseudoLowerBound.lean`(m=4) 与 `PseudoLowerBoundM5.lean`(m=5) 的私有
    `phase3_bound`/`s1..s5_pseudoLB` 同名同构——m 特化，已被 `PseudoLowerBoundGeneral` 取代
  - BinStretching 的 `OPT sigma = 1` 用非均匀调度（非常量负载），不适用新引理

## Session 2026-08-06（Rudin m=4 √3 形式化，进行中）

### Phase 1 ✅：参数化构造（Rudin.lean）

- `rudinV`（√3−1−ε）、`rudinM`（(3V−2)/2）、`rudinOK`（0<ε<1/100）
- 递推序列 `rudinS`/`rudinA`/`rudinB`/`rudinR`（rudinStep 迭代，B 依赖 R<V 分支）
- 数值界：V>√2/2、V>2/3、V<11/15、M∈(0,1/10)；√2/√3 有理界（含 √3<362/209）
- 递推恒等式：S_{i+1}=M·A_i、A_{i+1}=(A_i−2B_i)/4、A_i=2B_i+4A_{i+1}
- `rudinR_succ_of_lt`：继续情形 R_{i+1}=3/(4M)+1/2−1/(2MR_i)

### Phase 2 ✅：终止性（Lemma 3.2，编译通过）

- `rudinDelta_one`/`rudinDelta_one'`：δ₁=(2√3ε−ε²)/(4MV)；`rudinDelta_one_pos`：δ₁>11ε
- `rudin_R_step_sub`：f(R')−f(R)=(R'−R)/(2MR'R)（干净代数引理）
- `rudin_MVV_lt`：M·V²<1/19（√3<362/209 精细界）
- `rudinDelta_succ`/`rudinDelta_succ_gt`：δ_{i+1}=δ_i/(2MR_{i+1}R_i)>(19/2)δ_i
- `rudin_terminates`：反证法（假设 ∀i, R_i<V）→ 正性+递增不变量归纳 →
  δ 指数增长 → 几何级数下界 R_i ≥ R₀+δ₀·((19/2)^i−1)/(19/2−1) →
  (19/2)^i 无界（2^i≥i + Archimedean）→ 矛盾；∃n, V≤R_n
- 关键坑：`i+1` vs `i.succ`（kernel 不归约 Nat.add 上的 iterate，改用 i.succ + 显式转换）；
  rfl 的 reducible 透明度不展开普通 def，需先 rw 展开；√3³ 需 hsq3 引理

### 待办

- ~~Phase 3~~ ✅：Lemma 3.3 打包引理完成
- Phase 4a ✅：Lemma 3.4 数值引理（违规比率下界）
- Phase 4b：Lemma 3.4 运行追踪归纳（完整序列 + 违规前缀 + 逐层 runAlgorithm）
- Phase 5：Lemma 3.5 收尾 + 主定理 `rudin_m4_lower_bound`（替换 axiom）

### Phase 3 ✅：打包引理（Lemma 3.3，编译通过，commit c88ba0ce965）

- `rudinN`（Nat.find 终止索引）、`rudinN_spec/min/ratio_lt/pos`
- `rudin_pos_le_n`：继续前缀 i≤n 上 S/A/R>0 且 R₀≤R_i（复用 h_never 版本的归纳结构）
- `rudinB_le_half_A`：终止索引处 B_i = S_i−A_i ≤ A_i/2（R_i ≥ V ≥ 2/3）
- `rudin_packing`：层 n..i 可分 4 组 ≤ 3/2·A_i、3 组 ≤ 2A_i
  - 表述用负载向量（Loads 4 / Loads 3），避免列表打包的 Perm 论证
  - 基例（顶层 B_n×4+A_n×4）：4×[B,A] 与 3 组 [A,A],[A,B,B],[A,B,B]
  - 归纳步：新层 i−1 插入；3 组 {A,A},{A,B,B,X,X},{A+2A_i,B,B,X}，
    4 组 {A,B,X}×3+{A+2A_i,B}；用 A_{i−1}=2B_{i−1}+4A_i 与 B+2A_i=A/2
- 关键坑：`i+1` vs `i.succ` 的 Nat.add 归约（conv/unfold + omega 转换）；
  `Fin.sum_univ_three/four` 用 simp 展开；let（li/li'）要 dsimp 展开才能 rw

### Phase 4a ✅：Lemma 3.4 数值引理（编译通过，commit a382616671b）

- `rudin_B_ratio_gt`：B 层违规比率 2(M+1−4MR)/(1−MR) > 1+V
  （M<1/10, R<V<11/15；分 R>1/3 用 242/139>26/15 的链，R≤1/3 时比率≥2）
- `rudin_A4_eq`：A(M+5/2) = (1+V)·(3/2)A（第 4 作业 A_i+2A_{i+1} 碰撞，紧）
- `div_sub_ge`：x≥0, D≤N, D−x>0 ⟹ (N−x)/(D−x) ≥ N/D
- `rudin_A23_ratio_ge`：第 2/3 个 A_i 碰撞的比率 ≥ 1+V
- 坑：norm_num 对 ℝ 分数不等式需要显式类型标注（`(26/15 : ℝ) < ...`）；
  div_nonpos_iff 的分支类型，改用 rw [div_le_iff₀]

### Phase 4b 前置 ✅：构造可行性 + B 违规 OPT 界（commit a6f2640db17）

- **关键洞察**：B_i ≥ 0 不需要收紧 ε！B_i（继续）= S_i(1−R_i(1+M))，
  R_i < V < √(2/3) < 1/(1+M) → B_i > 0（任何 ε < 1/100）。
  之前用 q_i = A_i/A_{i−1} 推导 B 负是套错了层（把继续形式用到终止后）。
- `rudinV_lt_sqrt23`（V<√(2/3)，用 Real.lt_sqrt 平方保序）
- `rudinV_mul_one_add_M_lt_one`（V(1+M)<1 ⟺ V²<2/3）
- `rudinB_pos_lt_n`：继续路径 B_i > 0（关键可行性）
- `rudin_opt_le_B_violation`：B 违规前缀 OPT ≤ B_i+3/2·A_{i+1}
  （打包：2 台放 B_i + Lemma 3.3 的 4 组前缀打包）
- 剩余：R_n ≤ 1（终止层 B_n = S_n(1−R_n) ≥ 0 需要，需 δ 增长/时序分析）、
  A 违规 OPT 界（3/2·A_i 与 A_i+B_i 两个打包）、
  运行追踪归纳（逐层 runAlgorithm）、Lemma 3.5、主定理

## Session 2026-08-05

- 读取 Tan2015 论文全文（6 页），确认通用构造：f/g/x/q/β/γ、5 阶段 adversary、LB1/LB2/LB3
- 确认 m=4/5/6 现有证明是 q=1 特例，通用版本必须引入 q_m ≥ 2 与 LB3
- 审阅 PseudoLowerBound.lean / M5 / M6 / Basic.lean / Faigle.lean：
  - `layer_separation`、`layer_separation_from_base` 已通用化（m 参数化），Phase 1/2 可复用
  - 固定 m 文件的机级证明是显式枚举 Fin m，不能直接推广
- 计划：Phase 1（解析恒等式）→ Phase 2（根/q_m）→ Phase 3（Lemma 2.6）→
  Phase 4（LB 定义）→ Phase 5（adversary 机级证明）→ Phase 6（收尾注册）

## Session 2026-08-05（续）

### 完成：PseudoLowerBoundGeneral.lean Phase 1（单文件编译通过）

- 定义 `tanAlpha`, `cVal`, `fVal`, `gVal`, `x1Val`
- 恒等式 (3) `gVal_rec`、(4) `fVal_sum_geometric`、(5) `gVal_closed`、(7) `gVal_one`
- `gVal_one_eq_half`（x_1 公式）、`fVal_one_x1`（f_1(x_1) 值）
- Lemma 2.1: `fVal_strictAntiOn`（幂单调辅助 `pow_lt_pow_left_of_nonneg`）、
  `gVal_strictMonoOn`（导数：`cVal_deriv`/`fVal_deriv`/`gVal_deriv`/`gVal_deriv_pos`）
- 连续性/可微性辅助：`cVal_differentiableAt`, `fVal_differentiableAt`,
  `fVal_continuous`, `fVal_sum_differentiableAt`, `gVal_differentiableAt`, `gVal_continuousOn`

### 完成：Lemma 2.2（根的存在唯一性，编译通过）

- 端点：`gVal_lower_5_7`（g(5/7) ≤ 1/2）、`gVal_upper_top`（g(top) ≥ 1/2）
  - 伯努利二次不等式 `bernoulli_quadratic`（归纳 + `(n+1).choose 2` 递推）
  - `core_ineq`（奇偶分类：m=2r / 2r+1，nlinarith 收尾）
  - `choose_two_succ`、`topVal_one_add`、`cVal_top`、`fVal_top` 等代数辅助
- IVT：`exists_root_gVal_eq_half`（isPreconnected_Icc.intermediate_value 的图像版本）
- 唯一性：`exists_unique_root_gVal_eq_half`（严格单调）
- `xRoot m i`（Classical.choose）+ `xRoot_mem` / `xRoot_eq` / `xRoot_unique`
- 已注册到 `OnlineScheduling.lean`

### 完成：Lemma 2.3–2.5 + q_m/β_m/γ_m（Phase 2 收尾，编译通过）

- Lemma 2.3 `fVal_succ_ge_of_ge`（f_{i+1}(x_i) ≥ 1/2 ⟹ f_{i+1}(x_{i+1}) ≥ 1/2，
  用 (3) + 单调性 + 反证）
- Lemma 2.4 `fVal_t_succ_le`（f_{t+1}(x_t) ≤ 1/2，用 (5)、x_t < top（把 gVal_upper_top
  强化为严格 <）、x_t < 1）
- Lemma 2.5 `IsetAt_nonempty`（基例 f_1(x_1) > 1/2 via xRoot_one_eq；归纳步用 Lemma 2.3；
  最终与 Lemma 2.4 矛盾）
- `qVal`（Nat.find 最小元 + `qVal_min`）、`betaVal`、`gammaVal`
- `IsetAt_one_of_le_six` / `qVal_eq_one_of_le_six`（m=4,5,6 时 q_m=1）

### 完成：Lemma 2.6（Phase 3，编译通过）

- α 性质：`tanAlpha_sq`（α(α−1/2)=1/3）、`tanAlpha_pos`、`tanAlpha_ge_five_seven`、
  `tanAlpha_lt_one`、`tanAlpha_ge_eleven_fifteen`、`tanAlpha_ge_thirty_seven_forty_eight`
- γ/β 基本性质：`gammaVal_le_beta` / `gammaVal_le_alpha` / `gammaVal_ge_five_seven` /
  `gammaVal_le_one`
- (i) `fVal_gamma_chain`：f_{q+1}(β) ≤ 1/2 ≤ f_q(γ)，链 f_{j+1}(γ) ≤ f_j(γ)，f_q(γ) ≤ 1
- (ii) `gammaVal_mul_le_one_third`（γ≤α + h 单调 + α(α−1/2)=1/3）、
  `gammaVal_mul_le_one_half_sub`（m≥6 用 1/3 ≤ 1/2−1/m；m=4,5 直接算 γ=11/15, 37/48）
- (iii) `gammaVal_main_ineq`（g_q(γ) ≤ g_q(β)=1/2 + (5) 的部分和公式）

### 完成：Phase 4 主体（PseudoLB 定义 + σ1/σ2/σ3 前缀界，编译通过）

- `jthLargest`（`List.mergeSort` 降序 + `getD`），`LB3`（k=1..⌊(l−1)/m⌋ 的位置和 max），
  `PseudoLBGen = max(LB1, LB2, LB3)`
- 计数核心 `jthLargest_le_of_card_lt`：少于 j 个作业 > x ⟹ 第 j 大 ≤ x
  （`countP_ge_of_forall_getElem` 归纳 + mergeSort 排列/排序事实 + `SortedGE` 反单调）
- 辅助：`filter_replicate`、`maxJobSize_le_of_forall`、`maxJobSize_replicate`、
  `jthLargest_le_of_forall_le`、`aVal_lt_bVal`、`two_aVal_le_bVal`、σ2/σ3 的计数引理
- 序列：`aVal`/`bVal`/`σ1..σ5`；`aVal_add_bVal`、`aVal_add_two_bVal`、`bVal_lt_half` 等
- `PseudoLBGen_σ1 = a`、`PseudoLBGen_σ2 = γ−1/2`
- `LB3_σ3_le_two_b`：p_m,p_{m+1} ≤ b；p_{2m−1} ≤ b、p_{2m},p_{2m+1} ≤ a ⟹ ≤ b+2a ≤ 2b
- `LB1_σ3_le`：γ−q/2m = γ−(β²−f_{q+1}(β))/(1+β)（(5) + g_q(β)=1/2）≤ (γ+1/2)/(1+γ)
- `PseudoLBGen_σ3_le ≤ (γ+1/2)/(1+γ)`（LB1/LB2/LB3 三路）

### 踩坑记录（续）

- 与 m=4 文件重名 `PseudoLB` → 改名 `PseudoLBGen`
- 依赖 if（`if h : ... then sup' h ...`）不能用 `if_pos`（then 分支依赖 h），要用 `dif_pos`
- `List.filter_append` 对嵌套 append 需用两次
- `ω` 除法 `(m+m−1)/m = 1` 用 `Nat.div_eq_of_lt_le`（参数名 k/n/m 易混：m 是分子）
- `Nat.cast_sub` 需要 q ≤ m 才能把 `↑(m−q)` 拆开（nlinarith 视其为不同原子）
- `le_div_iff₀` vs `div_le_iff₀` 方向

### 踩坑记录（续）

- `field_simp` 对 `2*m - t` 分母会先换序成 `m*2 - t`，需同时传 `(m:ℝ)*2 - t ≠ 0`
- `∃! x ∈ s, P x` 的 choose_spec 结构是 `Q x ∧ ∀y, Q y → y = x`（Q = 元组）
- `IsPreconnected.intermediate_value` 的 a/b 是隐参，要 `(a := ...) (b := ...)`
- `nlinarith` 不自动展开 Nat 强制转换；`↑(i+1)` 与 `↑i+1` 是不同原子 → `push_cast`
- `ring_nf` 会把 `(n+1).choose 2` 的实参写成 `(1+n)`，导致原子不一致（改用 calc）

### 踩坑记录

- (3) 恒等式只对 i ≥ 1 成立（i=0 时 i·g_i = 0 ≠ Σf − C）
- `@[fun_prop]` 不能加在 def 上；改为给辅助 lemma 加属性
- `rw [fVal_deriv]` 对求和内绑定变量失效，用 `simp_rw`
- `field_simp` 需要显式传入 `m²−1 ≠ 0` 等分母条件
- `pow_le_one₀` 的指数 n 是隐参


### 续：OPT 公理不一致 —— 发现并修复（同日）

- 准备证 Table 7 打包时发现 `opt_le_of_schedule` 签名缺陷 → ProbeOPT.lean 证明
  旧公理集推出 False（OPT 坍缩为平均负载，与最大作业界矛盾）
- Basic.lean 新增 v2 可靠基础：`scheduleLoads` + `optMakespan`（分配上的具体最小值）
  + 5 个定理（le_schedule / le_of_schedule / ge_max_job / ge_avg / nonneg），编译通过
- BraunGraham2025.lean 迁移到新基础，编译通过（braun_opt_ge_F）
- 旧公理隔离（WARNING 注释），24 个遗留文件待迁移（清单见 findings.md）
- Table 7 打包证明顺延（依赖的正是新基础的 opt_le_of_schedule）

### 续 2：v2 基础完成 + 全库验证（2026-08-10）

- Basic.lean 打包机器就绪：`appendAssign`/`scheduleLoads_cons`/`scheduleLoads_append`
  （拼接序列负载 = 两半之和，归纳证明）、`diagAssignReplicate`/
  `scheduleLoads_replicate_diag`（replicate 对角分配每机恰一作业）
- 踩坑汇总（供 skill pitfalls 参考）：
  * Fin 结构 Prop 字段定义级证明无关：⟨v,p⟩ 与 ⟨v,q⟩ defeq，大量 Fin 相等步骤自动闭合
  * ite/dite 条件上的 rw 有 motive 问题 → 用 simp/if_pos/if_neg/split
  * `length ((p::σ)++τ)` 形式没有 OfNat (Fin ·) 0 实例 → 用显式 ⟨0, by simp⟩ 或
    类型标注 (0 : Fin (p :: (σ++τ)).length)
  * rw 匹配 ⟨0, by simp⟩ vs 字面 0 失败时，把引理陈述写成与目标同构的字面形式
  * Nat.sub 化简：(k+1)−(σ.length+1) 不定义归约，用 Nat.add_sub_add_right
- `maxJobSize_le_of_forall` 与 PseudoLowerBoundGeneral 同名 private 引理冲突
  → Basic 版本改 private 解决
- 全库逐模块串行构建通过（Scenarios 一次 I/O 抖动重试通过；并行构建在 G: 盘上
  持续随机 "failed to read file"——该盘读并发不稳，构建一律用串行/单线程）
### 下一步

Phase 4 余下：σ4_i（(γ+f)/(1+γ)）与 σ5（=1）的 PseudoLBGen 界 → Phase 5。

## Session 2026-08-05（续 2）
### 完成：Phase 4 收尾（单文件 + 全量 lake build 通过，EXIT=0）
- σ4_i 附属引理：`fVal_ge_half_of_le_q`、`fVal_succ_le`、`fVal_le_of_ge`、`fVal_one_gamma`、
  `phase4Sum`/`phase4_totalLoad`/`phase4Sum_split`/`phase4_gt_b`/`phase4_gt_a`
- σ4_i 计数与 PseudoLBGen 界：`count_gt_b/gt_a/gt_half_σ4`、`jthLargest_σ4_pos_le_*`、
  `div_two_σ4`、`LB1_σ4_le`、`LB3_σ4_le_two_b`、`LB3_σ4_q_le`、`LB2_σ4_le`、
  `fVal_le_one`、`PseudoLBGen_σ4_le`
- σ5 附属引理：`count_gt_b/gt_a/gt_half_σ5`、`jthLargest_σ5_le_b/a/half`
- `PseudoLBGen_σ5_le_one`：LB1 = Σp/m ≤ 1（用 `gammaVal_main_ineq` + `phase4Sum` 引入）；
  LB2 = maxJobSize ≤ 1（`LB2_σ4_le` + f_1 ≤ 1 + 收尾作业 1）；LB3 各位置计数 ≤ 3a+2b+1 ≤ 1
- 删除附属探针文件 Probe7.lean
### 踩坑记录（续 2）
- `simpa [hf1] using hle'` 在 1/2 谓词处失败：simp 把 1/2 规范化成 2⁻¹，而 hf1 左边仍是 1/2，
  无法匹配；改用 `rw [hf1]` + `rw [length=1]` + `omega`
- `rw` 能自动关闭 rfl 可得的目标，后续多余 `rfl` 会报 "No goals to be solved"
- `phase4Sum m hm (qVal m hm)` 与 `∑ j ∈ Icc 1 (qVal m hm)` 不是 def-eq，
  需要 `dsimp [phase4Sum]` 后 `rw [show qVal+1-qVal=1 by omega]` 才能用 gammaVal_main_ineq
- `hlb1` 内部不能先 `rw [htotal]`（否则 `le_trans hle' hle''` 不匹配目标）
- `Nat.div_eq_of_lt_le (k := 3) (n := m) (m := 3*m)` 收尾 hk 需要 `3*m < 4*m`（omega 从 4≤m 得出）

### 续：OPT 公理不一致 —— 发现并修复（同日）

- 准备证 Table 7 打包时发现 `opt_le_of_schedule` 签名缺陷 → ProbeOPT.lean 证明
  旧公理集推出 False（OPT 坍缩为平均负载，与最大作业界矛盾）
- Basic.lean 新增 v2 可靠基础：`scheduleLoads` + `optMakespan`（分配上的具体最小值）
  + 5 个定理（le_schedule / le_of_schedule / ge_max_job / ge_avg / nonneg），编译通过
- BraunGraham2025.lean 迁移到新基础，编译通过（braun_opt_ge_F）
- 旧公理隔离（WARNING 注释），24 个遗留文件待迁移（清单见 findings.md）
- Table 7 打包证明顺延（依赖的正是新基础的 opt_le_of_schedule）

### 续 2：v2 基础完成 + 全库验证（2026-08-10）

- Basic.lean 打包机器就绪：`appendAssign`/`scheduleLoads_cons`/`scheduleLoads_append`
  （拼接序列负载 = 两半之和，归纳证明）、`diagAssignReplicate`/
  `scheduleLoads_replicate_diag`（replicate 对角分配每机恰一作业）
- 踩坑汇总（供 skill pitfalls 参考）：
  * Fin 结构 Prop 字段定义级证明无关：⟨v,p⟩ 与 ⟨v,q⟩ defeq，大量 Fin 相等步骤自动闭合
  * ite/dite 条件上的 rw 有 motive 问题 → 用 simp/if_pos/if_neg/split
  * `length ((p::σ)++τ)` 形式没有 OfNat (Fin ·) 0 实例 → 用显式 ⟨0, by simp⟩ 或
    类型标注 (0 : Fin (p :: (σ++τ)).length)
  * rw 匹配 ⟨0, by simp⟩ vs 字面 0 失败时，把引理陈述写成与目标同构的字面形式
  * Nat.sub 化简：(k+1)−(σ.length+1) 不定义归约，用 Nat.add_sub_add_right
- `maxJobSize_le_of_forall` 与 PseudoLowerBoundGeneral 同名 private 引理冲突
  → Basic 版本改 private 解决
- 全库逐模块串行构建通过（Scenarios 一次 I/O 抖动重试通过；并行构建在 G: 盘上
  持续随机 "failed to read file"——该盘读并发不稳，构建一律用串行/单线程）
### 下一步
Phase 5：5 阶段 adversary 机级证明 `exists sigma, algorithmMakespan >= (1+gamma) * PseudoLBGen m sigma`

## Session 2026-08-05（续 3）
### 完成：Phase 5 机级 adversary 证明（单文件 + 全量 lake build 通过，EXIT=0）
- 辅助引理：`aVal_pos`/`bVal_pos`/`one_add_gammaVal_pos`、
  `Phase34Inv`（Phase 3-4 不变式：n≤1、Σn=t、n=0 → load=γ−1/2、n=1 → γ≤load）
- `phase34_step`：单个 ≥1/2 作业，碰撞（所选机器已有作业）→ makespan ≥ γ+p，
  否则不变式推进（Function.update n j 1 + Finset.sum_ite_eq' 处理 Σ）
- `σ4_succ_append`：σ4 (i+1) = σ4 i ++ [f_{q−i}]
- `phase3_loop`：对剩余计数 r 递归；碰撞 → 证 σ3 的界（makespan ≥ γ+1/2，
  prefix 单调性 `algorithmMakespan_mono` + `(1+γ)·PseudoLBGen σ3 ≤ γ+1/2`）
- `phase4_loop`：对剩余 r 递归；第 r+1 个作业大小 f_{r+1}；
  碰撞 → 证 σ4 (q−r) 的界（`PseudoLBGen_σ4_le` + `Nat.sub_sub_self` 处理下标）
- 主定理 `pseudo_lower_bound_general`：Phase 1/2 复用 `layer_separation`/
  `layer_separation_from_base`；Phase 3-4 用 loop；Phase 5 收尾作业 1：
  `pigeonhole_all_ones`（Σn=m、n≤1 → 全 1）→ 每机 load ≥ γ → makespan ≥ γ+1 ≥ (1+γ)·PseudoLBGen σ5
- 文件注册在 `OnlineScheduling.lean:50`；find-gaps 确认该文件无 sorry/axiom 残留
### 踩坑记录（续 3）
- 独立的 `have` 里 `1 / 2` 会被默认解析成**自然数除法**（`(1 : ℕ) / 2`），
  导致 `rw [hrep]` 在 runAlgorithm 目标里匹配失败（类型不同）；
  需显式写 `(1 / 2 : ℝ)`，或直接 `rw [List.replicate_succ']`（定理实例化不受影响）
- `constructor` 不会展开 `def` 类型的合取（Phase34Inv），需先 `unfold Phase34Inv`
- `A ∧ B ∧ C ∧ D` 右结合：`A ∧ (B ∧ (C ∧ D))`，构造子弹结构要匹配
- `rw [← hrest]` 会重写 `m - q - (t+1)` 内部的 `m - q` 子项；用 `congr 1; omega` 或 calc 替代
- `simpa [hseq] using hmono'` 在 `replicate_add` 是 simp 引理时会先合并 replicate 导致失配；
  改用 `rw [hseq] at hmono'`
- `use sigma` 会自动尝试 assumption 闭合剩余目标（hcert 在作用域内），后面再 `exact hcert` 会
  报 "No goals to be solved"；直接用 `exact ⟨sigma, hcert⟩`
- 嵌套减法 `q - (q - (r+1))` omega 不能分解（q−r 是原子），用 `Nat.sub_sub_self`

### 续：OPT 公理不一致 —— 发现并修复（同日）

- 准备证 Table 7 打包时发现 `opt_le_of_schedule` 签名缺陷 → ProbeOPT.lean 证明
  旧公理集推出 False（OPT 坍缩为平均负载，与最大作业界矛盾）
- Basic.lean 新增 v2 可靠基础：`scheduleLoads` + `optMakespan`（分配上的具体最小值）
  + 5 个定理（le_schedule / le_of_schedule / ge_max_job / ge_avg / nonneg），编译通过
- BraunGraham2025.lean 迁移到新基础，编译通过（braun_opt_ge_F）
- 旧公理隔离（WARNING 注释），24 个遗留文件待迁移（清单见 findings.md）
- Table 7 打包证明顺延（依赖的正是新基础的 opt_le_of_schedule）

### 续 2：v2 基础完成 + 全库验证（2026-08-10）

- Basic.lean 打包机器就绪：`appendAssign`/`scheduleLoads_cons`/`scheduleLoads_append`
  （拼接序列负载 = 两半之和，归纳证明）、`diagAssignReplicate`/
  `scheduleLoads_replicate_diag`（replicate 对角分配每机恰一作业）
- 踩坑汇总（供 skill pitfalls 参考）：
  * Fin 结构 Prop 字段定义级证明无关：⟨v,p⟩ 与 ⟨v,q⟩ defeq，大量 Fin 相等步骤自动闭合
  * ite/dite 条件上的 rw 有 motive 问题 → 用 simp/if_pos/if_neg/split
  * `length ((p::σ)++τ)` 形式没有 OfNat (Fin ·) 0 实例 → 用显式 ⟨0, by simp⟩ 或
    类型标注 (0 : Fin (p :: (σ++τ)).length)
  * rw 匹配 ⟨0, by simp⟩ vs 字面 0 失败时，把引理陈述写成与目标同构的字面形式
  * Nat.sub 化简：(k+1)−(σ.length+1) 不定义归约，用 Nat.add_sub_add_right
- `maxJobSize_le_of_forall` 与 PseudoLowerBoundGeneral 同名 private 引理冲突
  → Basic 版本改 private 解决
- 全库逐模块串行构建通过（Scenarios 一次 I/O 抖动重试通过；并行构建在 G: 盘上
  持续随机 "failed to read file"——该盘读并发不稳，构建一律用串行/单线程）
### 下一步
Phase 6：更新 `LOWER_BOUND_TODOLIST.md` 与 `docs/THEOREMS_ARCHIVE.md`（THEOREMS_ARCHIVE 需核对 89 条定理清单的状态）
