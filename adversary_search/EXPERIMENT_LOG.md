# 实验记录（服务器实验，autodl 32 核 / 377GB，2026-08-17）

## EXP-2026-08-17-A：LLM 模板生成 + 漏斗粗筛 + 修复循环首轮

**目的**：跑通"Qwen 生成对抗模板 → schema 校验 → 漏斗粗筛 → 失败修复循环"闭环。

**配置**
- 模型：qwen3.8-max（阿里云 Token Plan 网关 token-plan.cn-beijing.maas.aliyuncs.com，
  兼容模式 chat/completions，`--no-think`——思考模式在该网关挂起 7min+ 零输出）
- 漏斗阈值：coarse=1.70，fine=1.7320
- 代码版本：template-schema 分支 e27b861

**阶段 1：生成**
- 试验批 3 模板（no-think，45s）：3/3 schema 合法
- 正式批 20 模板：单次调用撞 max_tokens=8000 截断，raw_decode 抢救 17 个，17/17 合法
  （修复：分块 per-call=8 + 16k tokens）
- 多样性：FKT 族 5、Rudin 族 6、Braun 族 5、混合 2、新结构 2（达标）

**阶段 2：漏斗（20 模板）**
- KNOWN-BAND 1：`FKT_Base_m4` 盲复现 FKT，精确值 **1.7071 = 17071/10000** ✓
- REJECTED 3（<1.70，结构可展开）
- L2 拦截 15：**主导失败模式 = 负尺寸**（11/15，扰动代数后参数越出可行域），
  递推不终止 1、未定义名 1、求值异常 1
- CANDIDATE 0

**阶段 3：修复循环 R1（只给错误信息）**
- 15/15 schema 合法，但漏斗下 **0/15 真正修复**：负尺寸值与原错误完全相同
  （如 B=−0.024919... 逐位不变）——模型只重述了原代数，没动参数
- **结论**：单轮修复 + 纯错误反馈不工作

**阶段 4：修复循环 R2（prompt 注入约束流形知识）**
- 追加教学：V/M 耦合 M=(3V−2)/2、V=√3−1−eps；Braun c 的根区间；FKT 参数范围
- 12 个仍失败模板再修：schema 12/12 合法，漏斗下 **仅 1/12 存活**
  （FKT_Scaled_Final_r1 进 KNOWN-BAND）；Rudin 族 B 仍为负（−0.0249→−0.0253，
  参数动了但仍在流形外）
- **结论**：文本教学也救不了数值可行性——LLM 无法可靠地在约束流形上选参数

**核心发现（方法论层面）**
1. LLM 能盲复现经典构造（FKT 1.7071）→ 复现矩阵可行
2. LLM 的失败集中在**数值可行性**而非结构——印证分工原则"优化器找尺寸"：
   参数可行性应交给数值方法（eps 扫描 / DE + 正性惩罚），不该让 LLM 猜
3. 有效的 LLM 产出区间：FKT 族（参数少、可行域宽）；Rudin/Braun 族需要
   **结构化参数化**（模板只暴露 eps 等少自由度，其余由 defs 强制推导）
4. 漏斗本身全部按设计工作：L1/L2 拦截精确（每个失败都带可诊断的数值）、
   无误放、深层模板秒级

**资源消耗**：约 5 次 API 调用，总 token < 4 万（no-think 模式），费用可忽略

**下一步**
1. 模板 schema 增加"强制推导"约束：Rudin/Braun 族模板只允许暴露 eps/c 等
   生成元，其余量必须由 defs 表达式定义（schema 层校验）
2. 数值可行性求解器：对 REJECTED/L2 失败的模板，自动扫描自由参数
   （eps 网格 + 正性检查），不依赖 LLM
3. DE 精修 3 个 REJECTED 结构（尤其 FKT_ThreeLayer）

---

## EXP-2026-08-17-B：数值可行性修复（随机搜索 + DE + 分类诊断）

**目的**：L2 失败（负尺寸）是数值问题还是结构问题？能否不经 LLM、纯数值修复？

**方法**
1. 随机搜索：15 个失败模板 × 1000 采样点（materialize 全尺寸为正 = 可行）
2. DE（scipy differential_evolution，目标 = −min(作业尺寸)，
   template_schema.materialize 增加 check_positive=False 提供连续信号）
3. 分类诊断：每模板 60 点采样，区分"结构性异常"与"处处负尺寸"

**结果**
- 随机搜索：0/15 可行
- DE：0/15 可行（全部 0.0-0.2s 内判定，可行域为空时目标函数为常数）
- 分类诊断：**结构性异常 2**（未定义名/递推不终止），**处处不可行 13**
  ——包括 LLM 自认的"Braun_c1_Std 标准复现"（min_size=−1.72，结构本身就是错的）
- 典型证据：Rudin_Sqrt3_Std 把递推改成 B'=(S'−A'−M·A')/3，min_size≡−0.062
  与参数 V 无关——结构恒不可行

**核心结论（设计转向）**
1. LLM 的"结构变异"（改递推、改系数、改终止条件）几乎必然破坏可行性；
   失败是**结构性**的，任何参数优化都无法修复
2. 唯一存活的两个模板（FKT_Base 1.7071、FKT_Scaled_Final_r1）恰好都是
   **结构保守、只动尺寸**的 FKT 族——与结论 1 互为印证
3. **生成策略必须改为"受约束变异"**：
   - 递推/代数从 seeds/*.json 原样继承（锁死），LLM 只允许变：
     层数、eps、终作业系数、每层作业数（m 或 m−1）、层序
   - 即"LLM 选配置，不写数学"；结构合法性由构造保证，数值由 DE 精修
4. 薄流形上的可行性搜索（DE/随机）只在"结构固定、参数自由"时才有意义——
   正好是受约束变异模板的下游步骤

**资源**：本地计算（服务器 CPU），无 API 消耗；代码 feasibility_repair.py（DE 版）

---

## EXP-2026-08-17-C：受约束变异（LLM 选配置，不写数学）

**目的**：验证 EXP-B 的设计转向——递推代数锁死继承种子，LLM 只选安全旋钮，
能否实现 ~100% 可展开率，并测绘值对系数扰动的稳健性。

**配置空间**（Rudin 族，递推/层结构锁死）
- eps ∈ {0.009, 0.005, 0.001, 0.0005, 0.0001}
- final_mult ∈ {1,2,3}（终作业 = k×A_first，规范值 2）
- big_coeff ∈ {1,2,3}（大作业 = A+c×A_next，规范值 2）
- order ∈ {rev, fwd}

**结果 1：网格基线（45 配置，无 LLM）**
- 实例化 **45/45 = 100%**（自由生成 ~25%，修复循环后仍 <30%）
- 漏斗：KNOWN-BAND 5，REJECTED 40，CANDIDATE 0
- 存活者恰好是 5 个 eps × **(fm=2, bc=2, rev) 规范点**；
  其余 8 种系数组合 × 5 eps **全部 < 1.707**

**结果 2：LLM 旋钮模式（qwen3.8-max，1 次调用，817 completion tokens）**
- LLM 提议 12 个配置：3 个规范点（不同 eps）+ 单旋钮扰动 + fwd 对照——
  自发的假设扫描设计，与网格互为印证
- 实例化 **12/12 = 100%**；漏斗 KNOWN-BAND 3（规范点）、REJECTED 9
- fwd 变体探索了 67296 个状态才被拒（rev 只需 ~26）——层序影响搜索代价

**核心科学发现：√3 值是系数空间的孤立点**
final_mult 或 big_coeff 偏移 ±1，值立即坍缩到 1.707 以下（全部 40 个
非规范配置无一幸免）。这是对 MECHANISMS.md "代数坍缩"论点的直接数值验证：
经典构造的正确性不是区域性质，是孤立点性质——解释了为什么自由生成/修复
循环全部失败（任何代数改动几乎必然离开该点）。

**管线结论**
- 受约束变异管线全链路打通：LLM 提议 → 100% 实例化 → 秒级漏斗 → 自动归档
- 本旋钮空间内无超越规范构造的值（符合预期：孤立点）
- **真正的前沿**：要得到新值，必须构造**新的坍缩恒等式**（新的魔法常数+
  极小多项式），即在"结构+代数"层面创新而非系数层面——下一步方向：
  让 LLM 在 Mechanisms 探针的范式下提出新的恒等式候选，用符号验证+
  数值求值双通道筛选

---

## EXP-2026-08-17-D：魔法常数自动发现闭环（全部服务器执行）

**目的**：建立不依赖 LLM 写数学的自动发现引擎——优化找常数、整数关系猜代数、
精确重建验证。族：几何层塔（4×(s0·t^k), k=0..L−1，终作业 1）。

**方法**（identity_search.py）
1. DE 优化 (s0, t) 最大化精确 minimax 值（popsize=15, maxiter=40）
2. 猜代数：候选常数库匹配（小二次无理数 (a+b√D)/c）优先，mpmath PSLQ 兜底
3. 精确验证：极小多项式 → 60 位牛顿根 → 重建模板 → 精确复评

**结果**

| L | s0* | t* | 值* | t 身份 | s0 身份 |
|---|---|---|---|---|---|
| 2 | 0.207108 | 2.414202 | **1.7071058** | **1+√2**（z²−2z−1）✓ | **(√2−1)/2** ✓ |
| 3 | 0.495512 | 2.147899 | 1.6823278 | 弱匹配（~1e-4，疑伪） | 弱匹配 |

- L=2 在无任何提示下**自动复现 FKT 的两个魔法常数**（理论值 t=1+√2=2.4142136、
  s0=(√2−1)/2=0.2071068、值 1+√2/2=1.7071068），数值-理论符合 ~1e-6，
  精确重建验证通过
- **L=3 几何塔最优值 1.6823 < FKT 1.7071**：三层几何结构反而更差——
  FKT 的两层结构是该族内的最优，又一个"孤立结构"证据

**方法论结论**
1. 发现闭环全链路可用：数值最优 → 代数身份猜测 → 精确验证，零人工干预
2. 常数库+PSLQ 双通道比单一 PSLQ 稳健（DE 收敛精度有限时库匹配仍能命中）
3. 该引擎可直接用于更富的族（Rudin/Braun 参数化推广）——
   下一步的真正候选方向

**资源**：服务器 CPU，L=2 优化 3s，L=3 优化 55s，无 API 消耗


---

## EXP-2026-08-28-A：Tan-Li 伪下界构造的真 OPT 复测 + m=5 管线 Stage 0（M5-0）

**目的**：(1) 量化 Tan & Li (2015) q=1 五阶段伪下界构造在**真 OPT 语义**下的真实对抗强度
（此前只有伪界 26/15、85/48、9/5，从未测过真值）；(2) 按 M5_ADVERSARY_SKETCH 完成
Stage 0 冒烟与基线确认，为 m=5 主战场铺管线。

**方法**
- 新种子 `seeds/pseudo_m{4,5,6}.json`（γ 用 solve 精确锁定：11/15、37/48、4/5）、
  `seeds/fkt_m5.json`；`template_eval.py` 精确 minimax（min_调度器 max_前缀，真 OPT 枚举）
- `identity_search.py` 增加 `--m` 参数（原硬编码 m=4，11 处替换）；
  `pattern_opt.py` 本就支持 `--m`
- 环境：autodl 32 核 CPU 实例（无 GPU），/root/LLM-FOR-SCHEDULING，Python 3.10.8（miniconda）

**结果 1：伪构造真值（精确模式）**

| 模板 | m | 作业数 | 伪上界 | **真值** | gap | 状态数 | 耗时 |
|---|---|---|---|---|---|---|---|
| pseudo_m4 | 4 | 13 | 26/15 ≈ 1.7333 | **585/358 ≈ 1.6341** | 0.099 | 18,401 | 0.1s |
| pseudo_m5 | 5 | 16 | 85/48 ≈ 1.7708 | **3264/1969 ≈ 1.6577** | 0.113 | 228,345 | 1.0s |
| pseudo_m6 | 6 | 19 | 9/5 = 1.8 | **8/5 = 1.6** | 0.200 | 1,596,684 | 8.7s |
| fkt_m5 | 5 | 11 | — | **1.7071 = 17071/10000** ✓ | — | 1,140 | 0.0s |

**结果 2：Stage 0 冒烟（引擎验证）**
- `m4_search --m 5 --grid 1,2 --depth 8` → 3/2（1808 节点 0.02s）；
  `--grid 1,2,3` → 3/2（16024 节点 0.19s）——整数网格封顶，与 m=4 经验一致
- `pattern_opt --m 5 --baseline`：FKT (0.2071,0.5,1) → **1.707** ✓；
  扰动 (0.25,0.5,1) → 5/3——FKT 尺寸脆弱性在 m=5 复现

**核心发现**
1. **伪界与真值严重脱节**：m=5 真值仅 1.6577，比伪上界 85/48 低 0.113，
   甚至低于 FKT 的 1.707。原因：停止前缀的真 OPT 远大于 PseudoLB=max(avg,maxjob)
   ——伪框架"对抗强度"是证明技术意义上的，不是真实对抗强度
2. **真值对 m 非单调**（1.634 → 1.658 → 1.6）：机器越多装箱自由度越大，
   同一构造的比值被稀释。Tan-Li 构造**不能**作为 m≥5 真下界的种子候选
3. **F1 几何塔 DE 在 m=5 掉坑**：L=2 全预算（popsize=15, maxiter=40）
   收敛到 t=2.0、值 1.5 的局部最优，**错过 FKT 点**（t=1+√2，1.7071）——
   m=4 同预算能无提示复现 FKT（EXP-D），说明 m=5 目标面局部最优更多，
   需要多起点/更大预算
4. 对 M5 主线的含义：超越 1.748334（Rudin 2001 论文值）必须靠
   F3（Rudin 式递推）/F4（Braun 式陷阱）结构创新，伪下界族已排除

**进行中**（后台）
- F1 几何塔 L=3/L=4（identity_search --m 5，/tmp/id_m5.log）
- 自由尺寸搜索 k=3（pattern_opt --m 5 --k 3，8 workers，/tmp/popt_m5_k3.log）

**代码**：identity_search.py（+--m）；seeds/pseudo_m{4,5,6}.json、seeds/fkt_m5.json
（均已同步服务器）。工程坑：PowerShell `Set-Content -Encoding UTF8` 带 BOM，
json.load 拒绝——种子文件必须无 BOM 写入

---

## EXP-2026-08-28-B：Rudin 2001 论文到手 + m=5 构造序列数值验证（进行中）

**重大进展**：通过浙大图书馆 WebVPN/ProQuest 获取 Rudin 2001 博士论文全文
（*Improved Bounds for the Online Scheduling Problem*, UT Dallas, 102 页，
papers/_inbox/Improved_bounds_for_the_online.pdf，3.06MB 微缩胶片扫描件）。

**论文核心内容提取**
1. **Table A1（全部新下界）**：m=4: √3=1.7320508；m=5: **1.74833497030641**；
   m=6: 1.77409792411；m=7: 1.792667559；m=8: 1.803471135；m=9: 1.80896128；
   m=10: 1.81432683354；m=12: 1.8252768572641；m=14: 1.83679075816032；
   m=16: 1.84299410215536；m=24: 1.85669916563964；m=120: 1.875；m=3600: 1.88
2. **Table A2-A8**：m=5..12 的完整对抗作业序列表（尺寸+重数+除数列）
3. **层分类方法论**：Type 1 层（=FKT 机制，上限 √2/2）、Type 2 层（上限比
   ~1.7374）、Type 3 层（大终作业压 R，m=4 无效因上限 0.712<0.732，m≥5 必需）；
   m=5 最优 = 5 个 Type 2 层 + 1 个 Type 3 层（Table 13）；V 由多项式方程定
   （m=6 例：2V³+V²+4.5V−5=0 → V=0.77301984843995）
4. **Chapter 8 层方法极限**：R 变量需压到 1/(2V)；约束 = A 层末总载 < m−1，
   可用余量 m−1−mV 决定 V 上限；Table 14 给出层数→V 理论上界表

**m=5 序列验证（进行中）**
- Table A2 提取：21 种尺寸 71 作业（重数模式 5,5,5,5,4,1,5,4,1,...,4,1,1），
  生成种子 seeds/rudin2001_m5.json
- **工程坑 1（浮点归一化爆炸）**：首版种子用 60 位 Decimal 归一化 → 分母
  LCM 达 10^147 → OPT 分支定界崩掉（10 分钟超时）。修复：论文十进制串直接
  ×10^13 转精确整数（22 位），无浮点误差
- **交叉验证通过**：整数种子的 opt(前 20 作业各前缀) 与论文"除数"列逐位一致
  （如 prefix10 OPT = 242947127733683 = 论文 s1+s2）→ OCR 提取正确
- **性能画像**：prefix OPT 耗时 5→10→...→50 作业 = 0→0→0.07→0.96→12.9s
  （组合爆炸），全 71 前缀预计 30-60 分钟 → check 以 nohup 后台运行
  （/tmp/check_m5.log，tau=1.748334）

**同期：F1 几何塔 m=5**（identity_search）
- L=2: DE 掉局部最优 1.5（错过 FKT 1.707）；L=3: 1.5（重建 1.633，t=1+√3 命中）；
  L=4 运行中
- 自由尺寸搜索（pattern_opt k=3 m=5）：单次求值 >80min 不收敛，已终止
  ——教训：m=5 深度 16 网格 minimax 超出当前引擎能力，自由搜索路线对 m≥5
  需要先升级引擎（alpha-beta/支配剪枝），暂挂

**下一步**
1. check_m5 结果 → 若 PASS：m=5 构造获数值证书，进入有理化+Lean 形式化规划
2. 若 FAIL：按层二分定位 OCR 错误/自适应分支问题
3. m=6/m=7 序列种子（Table A3/A4）同法验证

### 补充（12:30）：m=7 验证 **PASS** 🎉

- 种子 seeds/rudin2001_m7.json（Table A4，57 作业 13 尺寸，×10^14 整数化）
- check tau=1.7926675：**PASS**，memo=159 状态，viol=90，Phase 2 耗时 0.0s
- 意义：Rudin 2001 的 m=7 下界 1.792667559 获独立数值验证；
  验证管线语义（固定序列+前缀 max）与论文自适应构造完全吻合；
  构造极紧（所有调度路径秒撞违例前缀）
- 并行：m=5（tau=1.748334）、m=6（tau=1.7740979，Table A3 由 200dpi
  页面图像人工核对重建，91 作业）Phase 1 进行中
- 驱动通用化：check_rudin.py（--seed/--tau/--cache 参数化）

### 补充（16:45）：m=5 验证 **PASS** + 目标升级

- m=5：RESULT: PASS tau=1.748334（memo=6909, viol=4746, Phase 2 0.0s）——
  Rudin 2001 m=5 下界获独立数值验证
- m=6：Phase 1 至 prefix 77/91，尾部单前缀耗时 1337→2811s 递增，
  串行超 12h 上限；缓存保 77 前缀；对策=前缀并行（未执行，待批）
- 目标升级：超越论文（>1.74833497030641）。策略记录于
  docs/research/M5_ADVERSARY_SKETCH.md v0.2 补遗（R1-R4 路线）

---

## EXP-2026-08-28-E: Rudin 2001 finite-sequence validation (m=5,6,7)

**Purpose**: independently evaluate fixed sequences from dissertation Tables A2--A4 using exact integer job sizes, exact OPT for every prefix, and the scheduler-side minimax recursion.

**Method**
1. Transcribe each table to a JSON seed and scale all decimal sizes to integers.
2. Compute and persist `OPT(prefix i)` for every prefix.
3. Check whether every scheduler response reaches the rational threshold at some prefix; cache symmetric sorted load states.

**Results**
- m=5: 71/71 prefix OPTs; `tau=1.748334`; **PASS**; 6,909 states.
- m=7: 57/57 prefix OPTs; `tau=1.7926675`; **PASS**; 159 states.
- m=6: 81/91 prefix OPTs; stopped after prefix 81 (8,083 seconds for that prefix); **incomplete, no lower-bound claim**.

Late prefix OPT computation dominates runtime. The resumable m=6 cache is preserved but is named `.partial.json`, and `check_rudin.py --cache-only` reports the ten missing prefixes without accidentally restarting the run. See [`RUDIN2001_RESULTS.md`](RUDIN2001_RESULTS.md) for the authoritative report.

**Invalidated side experiment**: the first m=5 geometric-tower run did not pass `m` into job construction or algebraic identity rebuilding. Its reported values therefore mixed m=4 and m=5 semantics and are excluded. The propagation bug is fixed and regression-tested; no new m=5 identity is claimed.

---

## EXP-2026-08-31-F: m=5 singleton-position neighborhood

**Purpose**: test a small, interpretable structural neighborhood around Rudin Table A2 before changing any job sizes. In each of the six `4+1` mixed blocks, move the singleton to any of the five positions while preserving every block and the complete job multiset.

**Method**
- Exhaustive configurations: `5^6 = 15,625`.
- Exact threshold:
  `1748334970307/1000000000000 = 1.748334970307`, strictly above Rudin's displayed `1.74833497030641`.
- Prefix OPT values keyed by `(m, sorted exact integer prefix)` so a cached value is reused only for the identical prefix multiset.
- All 71 baseline prefix OPT values were imported from the independently verified Rudin cache; 24 additional altered-prefix multisets were solved exactly.

**Result**
- `pass_count = 0`; state counts ranged from 72 to 208.
- The unchanged ordering also fails at this above-bound threshold, as expected.
- Artifact: `results/m5_structured/singleton_permutations_above_rudin.json`.

**Scope of the negative result**: this rules out only singleton reordering inside the six existing blocks. It says nothing about altered sizes, split/merged layers, terminal multipliers, or additional Type-3 layers. The next search must change a genuine structural interface rather than order alone.

---

## EXP-2026-08-31-G: m=5 late-interface exact shortlist

**Purpose**: test whether small, coupled size changes at Rudin Table A2's last
four interfaces can cross the displayed bound without changing the earlier
layer structure. The four multipliers control the last Type-2 singleton, the
four equal Type-3 base jobs as one group, the Type-3 singleton, and the final
job.

**Method**
- Enumerated 6,560 non-identity multiplier configurations on the exact grid
  `[0.999, 1.001]`.
- Used necessary lower-bound and representative-path screens only to rank the
  grid; these screens were explicitly non-certifying.
- Selected ten finalists and computed all 60 distinct candidate-specific exact
  prefix OPT values at lengths 65--71. The work completed locally; no paid
  server was started.
- Ran the exact fixed-sequence threshold game at
  `1748334970307/1000000000000 = 1.748334970307`.

**Result**
- Exact finalists: 10; PASS: **0**.
- Every exact check terminated after 72 memoized states with a scheduler escape
  path through all 71 jobs and no threshold-violating state on that path.
- The strongest explicit escape path among the ten reaches only
  `1.7478110647740217` (at prefix 71), below Rudin's displayed value.
- Artifacts:
  `results/m5_structured/late_interface_opt_results.json` and
  `results/m5_structured/late_interface_exact_check.json`.

**Scope of the negative result**: this certifies failure only for the ten exact
finalists. A subsequent full-grid safe-denominator certification, recorded
below as EXP-K, closes the other 6,550 configurations. Combined with EXP-F, the
result indicates that the next useful neighborhood should change the layer
mechanism itself rather than only reorder or rescale the existing suffix.

---

## EXP-2026-08-31-K: complete late-interface multiplier grid

**Purpose**: close the scope gap in EXP-G for every one of the 6,560 coupled
suffix-rescaling configurations without paying for unnecessary final-prefix
OPT computations.

**Method**
- A basic-lower-bound least-loaded path rejects 6,061 of 6,560 candidates.
- Accumulated content-addressed exact OPT values mixed with safe basic lower
  bounds reject another 218, leaving 281 candidates.
- For each remaining candidate, run the complete scheduler-placement recursion
  using exact OPT where cached and
  `max(largest job, ceil(prefix sum / 5))` everywhere else.
- These denominators never exceed exact OPT. Therefore this bounded game is
  easier for the adversary than the true threshold game: a scheduler escape in
  it is a rigorous escape in the true game. Conversely, a bounded-game PASS
  would be treated only as unresolved.

**Result**
- Remaining bounded games: 281; scheduler escapes: **281**; unresolved: **0**.
- State range: 75--172.
- Largest ratio upper bound on any resulting escape path:
  `125759586191744747937/71931059166370370000 =
  1.7483349703064097...`, strictly below
  `1748334970307/1000000000000 = 1.748334970307`.
- Complete grid: 6,560 tested; PASS: **0**.
- The 268-key final-prefix exact run was stopped because this stronger safe
  certificate made it unnecessary.
- Main artifact:
  `results/m5_structured/late_interface_remaining_safe_game.json`.

**Scope of the negative result**: every explicit point in the stated four-group
`[0.999, 1.001]` grid is ruled out. This says nothing about a finer grid,
larger perturbations, a coupled layer re-derivation, or a new packing mechanism.

---

## EXP-2026-08-31-H: two-Type-3-shaped scaled-copy pilot

**Purpose**: perform a zero-heavy-OPT pilot on an explicit 76-job family before
attempting to derive a full two-Type-3 tableau. Insert one rationally scaled
copy of the published five-job Type-3 block immediately before the original.

**Precision rule**: for `q=p/r>1`, multiply the whole published sequence by `p`
and the inserted block by `r`. This represents relative scale `1/q` exactly and
never rounds the inserted jobs independently.

**Grid and result**
- `q = 1001/1000, ..., 1100/1000`: 100 candidates.
- All 100 have a certified least-loaded-machine escape path below
  `1748334970307/1000000000000` using only the rigorous basic lower bound on
  each prefix OPT; exact candidate-specific OPT computation was unnecessary.
- Artifact: `results/m5_structured/two_type3_scaled_probe.json`.

**Interpretation**: this family is deliberately labeled *Type-3-shaped*, not a
Rudin two-Type-3 construction. The available dissertation transcription gives
the reverse ratio map but not the full two-layer state transitions, mixed job
rows, and packing certificates. Consequently this finite negative result does
not test the theoretically meaningful two-Type-3 recurrence. Moreover, a close
read of Table 13 corrects the earlier research premise: Rudin explicitly says
that, for the optimized m=5/m=6 tableau, replacing a Type-2 layer with another
Type-3 layer raises the late job sizes and gives an inferior solution. Table 14
is only an R-recurrence layer-count limit, explicitly “not fully tested
solutions.” A useful new Type-3 direction therefore needs a different packing
mechanism, not merely one more published-style row.

---

## EXP-2026-08-31-I: exhaustive late-interface order surgery

**Purpose**: close the remaining order-only gap around Rudin's last Type-2 and
Type-3 interfaces before changing sizes. Keep jobs 1--60 fixed and enumerate
all unique orders of the eleven-job multiset `XXXXtAAAAsf`.

**Method and result**
- Distinct orders: `11!/(4!4!) = 69,300`.
- Content-addressed late prefixes: 199 distinct multisets; 19 cached and 180
  newly solved exact OPT values.
- Exact threshold:
  `1748334970307/1000000000000 = 1.748334970307`.
- **PASS: 0**; threshold-game state range 72--76; complete screen took about
  21.5 seconds after prefix OPT preparation.
- Artifact: `results/m5_structured/late_interleavings_exact_check.json`.

**Scope**: this exhausts every ordering of the published final two blocks plus
final job while preserving their multiset. Together with EXP-F it gives strong
finite evidence that pure order surgery around Table A2 is exhausted. It does
not address changed sizes, added/removed jobs, or a new offline packing
mechanism.

---

## EXP-2026-08-31-J: single-job Type-2 4+1 size split

**Purpose**: test a genuine size surgery rather than another order-only change.
In one of the five Type-2 B blocks, select one of its five equal jobs and apply
an exact multiplier `k/1000`, for `k=900..1100` excluding identity.

**Result**
- Candidates: `5 stages × 5 positions × 200 multipliers = 5,000`.
- All 5,000 have a rigorous least-loaded-machine scheduler escape below
  `1.748334970307`, even when exact OPT is replaced by its smaller basic lower
  bound. Therefore no exact candidate-specific OPT work was necessary.
- Artifact: `results/m5_structured/type2_split_probe.json`.

**Scope**: this rules out only a one-job `5→4+1` split with all other sizes
fixed. A meaningful next split must couple the B change to the following A and
singleton values or derive a new exact packing identity.

---

## EXP-2026-08-31-L: coupled final Type-2 block grid

**Purpose**: test the coupled size change suggested by EXP-J. Jointly perturb
the final Type-2 block's five B jobs, four A jobs, and singleton while retaining
the published Type-3 block and final forcing job.

**Grid and method**
- Each group multiplier ranges from `9950/10000` through `10050/10000` in steps
  of `5/10000`; omit the all-identity point.
- Candidates: `21^3 - 1 = 9,260`.
- A least-loaded scheduler path with the safe basic OPT lower bound rejects
  8,141 candidates, leaving 1,119.
- Run the complete scheduler-placement recursion on every survivor, using
  content-addressed exact OPT where already available and the basic lower bound
  elsewhere. A bounded-game escape is rigorous because all denominators are at
  most exact OPT; a bounded-game PASS would count only as unresolved.

**Result**
- Survivor games: 1,119; scheduler escapes: **1,119**; unresolved: **0**.
- Complete grid: 9,260 tested; PASS: **0**.
- State range: 75--192.
- Largest escape ratio upper bound:
  `125759586191744747937/71931059166370370000 =
  1.7483349703064097...`, at the unchanged prefix 60 and strictly below the
  target `1.748334970307`.
- Artifact: `results/m5_structured/final_type2_coupled_safe_game.json`.
- Earlier partial final-prefix OPT files are not needed by this certificate.

**Scope**: this closes exactly the three-group local grid around the final
Type-2 block. It does not cover a finer or wider parameter grid, simultaneous
changes to earlier layers, or a formula-derived packing mechanism.

---

## EXP-2026-08-31-M: coupled grids across all Type-2 stages

**Purpose**: determine whether the coupled B/A/singleton surgery from EXP-L can
help at an earlier one of the five published Type-2 stages.

**Precision and grid**
- Perturb one stage at a time; multiply the full sequence by 10,000 and replace
  the selected stage's group factors by exact integer numerators. This avoids
  all per-job division or rounding.
- Three group multipliers per stage, each in
  `9950/10000, 9955/10000, ..., 10050/10000`; omit identity.
- Candidates: `5 × (21^3 - 1) = 46,300`.

**Result**
- Basic-bound least-loaded scheduler escapes: 40,693.
- Survivors: 5,607, split by stage as
  `1,131, 1,119, 1,119, 1,119, 1,119`.
- Complete mixed-bound scheduler games: 5,607; escapes: **5,607**;
  unresolved: **0**; PASS: **0**.
- State range: 6,945--12,299.
- Largest exact path-ratio upper bound:
  `1054856925963865625/603349440398708736 =
  1.7483349703064101...`, strictly below
  `1748334970307/1000000000000`. The maximum occurs at the unchanged prefix 15,
  before the first Type-2 stage can be affected.
- Artifacts: `results/m5_structured/type2_coupled_grid.json`,
  `type2_coupled_survivors.json`, and `type2_coupled_safe_game.json`.

**Scope**: every point in each one-stage local grid is rigorously ruled out.
This does not cover simultaneous changes to several stages, a finer/wider grid,
or a re-derived recurrence and offline packing proof.

---

## EXP-2026-08-31-N: coupled initial three-block grid

**Purpose**: test whether small joint size changes in the three equal five-job
blocks before the first Type-2 stage can improve the complete 71-job sequence.

**Method and result**
- Three group multipliers, each ranging from `9950/10000` to `10050/10000` in
  steps of `5/10000`; omit identity.
- Candidates: `21^3 - 1 = 9,260`.
- Exactness: scale every job by 10,000 and use the multiplier numerators on the
  selected blocks; no division or rounding.
- All 9,260 are rigorously rejected by a least-loaded scheduler path using the
  basic lower bound on prefix OPT. There are no survivors and no candidate OPT
  computations.
- Largest path-ratio upper bound:
  `33218540441529816435631165/19000100670473869822263296 =
  1.7483349703063091...`, at prefix 71 and strictly below the target.
- Artifact: `results/m5_structured/initial_coupled_grid.json`.

**Scope**: this closes only the three independent initial-block multipliers on
the stated grid. It does not alter multiplicities/order or re-derive downstream
Type-2 sizes and packing identities.

---

## EXP-2026-08-31-O: shared perturbation across all Type-2 stages

**Purpose**: test a coordinated proxy for changing Rudin's repeated Type-2
mechanism. Apply one common B/A/singleton multiplier triple simultaneously to
all five Type-2 stages.

**Result**
- Grid: `21^3 - 1 = 9,260` exact candidates.
- Basic-bound least-loaded path escapes: 8,141.
- Complete mixed-bound games on survivors: 1,119; escapes: **1,119**;
  unresolved: **0**; PASS: **0**.
- State range: 6,945--31,398.
- Largest escape ratio upper bound:
  `1054856925963865625/603349440398708736 =
  1.7483349703064101...`, at unchanged prefix 15 and strictly below target.
- Artifacts: `results/m5_structured/all_type2_shared_grid.json`,
  `all_type2_shared_survivors.json`, and `all_type2_shared_safe_game.json`.

**Scope**: this is a shared-multiplier family, not a formula-derived new
recurrence. It rules out only these coordinated relative rescalings. Future
work needs changed recurrence parameters, multiplicities, or packing identities.

---

## EXP-2026-08-31-P: inserted Type-2-shaped block

**Purpose**: perform an explicit-sequence pilot for an additional Type-2 block
before deriving a true sixth-layer recurrence. Insert a rationally scaled copy
of the final published ten-job Type-2 block immediately before Type-3.

**Method and result**
- For `q=p/r`, scale the published sequence by `p` and the inserted copy by `r`;
  its relative size is exactly `1/q`, without rounding.
- Grid: `q=1.200,1.201,...,2.000`; 801 sequences of 81 jobs.
- Basic-bound least-loaded scheduler escapes: 365.
- Complete basic-bound games: 436; escapes: **436**; unresolved: **0**;
  PASS: **0**.
- Each survivor game visits 85 states. The largest escape ratio upper bound is
  `124035018344733941032887/76475405198646660500000 =
  1.621894228903398...`, at prefix 76.
- Artifacts: `results/m5_structured/inserted_type2_probe.json`,
  `inserted_type2_survivors.json`, and `inserted_type2_safe_game.json`.

**Scope**: this copied block is only Type-2-shaped. It does not reconstruct the
successor Type-3/final sizes or establish the packing tableaux of a true sixth
Type-2 layer. The result rules out only the stated copied-block scale family.
