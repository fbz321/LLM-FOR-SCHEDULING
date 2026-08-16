# 自适应实例机制速查表（Mechanism Probes）

> 每个经典在线调度下界构造一行：魔法常数 + 极小多项式 + 比值坍缩。
> 对应本目录的 `*Key.lean` 探针——每个只 `import Mathlib`、秒级编译、0 sorry，
> 不重证全部调度定理，只蒸馏"为什么这个比值正确"的代数心脏。

| 构造 | 探针 | 魔法常数 | 极小多项式 | 比值坍缩 |
|---|---|---|---|---|
| Braun–Chung–Graham 2025, Thm 1（渐近 √3）| `BraunKey.lean` | α = 1+√3 | α² − 2α − 2 = 0 | 比值 = √3 − 余项(r)，r 指数衰减 → 渐近 √3 |
| Braun–Chung–Graham 2025, Thm 2（绝对 c₁）| `BraunAbsKey.lean` | c₁ ≈ 1.73102 | 6c³ − 28c² + 38c − 13 = 0 | 绝对比 = c₁（c₁·F = Σ+F）|
| Rudin 2003, m=4 | `RudinKey.lean` | V = √3−1，M = (3V−2)/2 | V² + 2V − 2 = 0 | 比值 = 1+V = √3−ε |
| Faigle–Kern–Turán, m≥4 | `FKTKey.lean` | fkt = 1+√2/2 | 2x² − 4x + 1 = 0 | 碰撞比 (a+2b)/(a+b) = fkt |
| Tan–Li 2015, m≥4（伪下界）| `TanLiKey.lean` | α = (3+√57)/12 | 6x² − 3x − 2 = 0 | 比值 = 1+γ_m，γ_m = min(β_m, α) ≤ α |

## 共同骨架

所有经典在线调度下界的正确性 = **「魔法常数由极小多项式唯一锁定 → 常数让比值精确坍缩」**：

1. 每个构造有一个（或两个）魔法常数，满足一个极小多项式（代数方程）；
2. 该常数在正实轴上**唯一**（另一根为负/越界被排除）——这就是"为什么常数只能取这个值"；
3. 常数让某个碰撞 / 强制路径的比值**精确**坍缩到目标（√3、c₁、1+V、fkt、1+γ_m）。

分工（见 `findings.md`）：**LLM 提结构，优化器找尺寸，Lean 证代数**。
本目录的探针就是"证代数"的最小可验证单元——每个探针把完整证明（几千行）压缩到
几十行，只保留魔法常数与坍缩恒等式。

## 编译

每个探针只 `import Mathlib`，不依赖项目库、不进全库 `lake build`：

```bash
cd OnlineScheduling
lake env lean Mechanisms/BraunKey.lean     # 或 BraunAbsKey / RudinKey / FKTKey / TanLiKey
```

秒级编译（≈ 24s），`EXIT=0`、0 sorry/axiom。
