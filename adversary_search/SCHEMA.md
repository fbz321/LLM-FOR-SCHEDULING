# 对抗模板 JSON Schema v1（C0 模板层数据格式）

> 本文件同时是 **LLM 生成模板时的 prompt 附件**：照此格式填空即可。
> 校验/展开：`template_schema.py`；求值：`template_eval.py --template <file>`。

## 一个模板 = 结构 + 参数 + 代数约束

```json
{
  "schema_version": 1,
  "name": "简短名字",
  "description": "结构说明：层模式、递推、与哪个已知构造的关系、变异点",
  "m": 4,

  "params":  [ { "name": "a", "value": 0.207, "free": true, "bounds": [0.05, 0.5] } ],
  "solve":   [ { "name": "c", "equation": "6*c**3 - 28*c**2 + 38*c - 13", "guess": 1.73 } ],
  "defs":    [ { "name": "S0", "expr": "(c-1)/(2-c)" } ],

  "recurrence": {
    "init": { "S": "1", "A": "1/(2*V)", "B": "1 - A - M*A" },
    "step": { "S": "M*A", "A": "(A-2*B)/4", "B": "where(A/S >= V, S-A, S-A-M*A)" },
    "until": "A/S >= V",
    "max_iter": 60
  },

  "layers": [
    { "loop": { "var": "i", "from": 0, "to": "n" },
      "emit": [ { "repeat": 4, "size": "B" },
                { "repeat": 3, "size": "A" },
                { "repeat": 1, "size": "where(i==n, A, A+2*A_next)" } ] },
    { "emit": [ { "repeat": 4, "size": "S0" } ] }
  ],

  "final": [ { "repeat": 1, "size": "2*A_first" } ],
  "order": "rev"
}
```

## 字段说明

| 字段 | 必需 | 说明 |
|---|---|---|
| `schema_version` | ✅ | 固定为 1 |
| `name` / `description` | ✅ | description 必须写明"以哪个已知结构为种子、变异点是什么"（去重用） |
| `m` | ✅ | 机器数（当前求值器支持 m=4） |
| `params` | 可选 | 数值参数。`free: true` + `bounds` = DE 可优化的自由参数；否则固定值 |
| `solve` | 可选 | 代数参数：牛顿法解 `equation = 0`（给 `guess`）。**代数约束在这里声明** |
| `defs` | 可选 | 按序求值的表达式定义，可引用 params/solve/前面的 defs |
| `recurrence` | 可选 | 层递推（Rudin 式）。`init` 顺序赋值；`step` 顺序赋值（后定义的可见先定义的新值）；`until` 在新状态上判断；终止时 `n` = 层数−1 |
| `layers` | ✅ | 层列表。每层 `emit` = 作业条目列表（按序发放）；带 `loop` 的层在递推状态上循环（`i`、`n`、状态名 = 第 i 层状态、`<名>_next` = 第 i+1 层状态） |
| `final` | 可选 | 层序列之后的终作业。可用 `<名>_first`/`<名>_last`（递推首/末状态） |
| `order` | 可选 | `fwd`（默认，层列表顺序发放）或 `rev`（层列表逆序发放）。**层序是结构的一部分**：Rudin rev=√3、fwd 只有 5/3 |

## 表达式语言

- 数字、变量、`+ - * /`、`**`（幂，**必须用 `**`，`^` 是 Python 位异或**）、一元负号
- 比较 `>= <= == != > <`（只用在 where 条件里）
- `where(cond, a, b)`：**惰性**求值，只算选中分支（未选中分支可含非法引用，如末层的 `A_next`）
- `sqrt(x)`、`abs(x)`
- 算术按 60 位 Decimal，最终有理化（分母 ≤ 10^20）

## 语义（求值器做什么）

模板展开为固定作业序列 σ 后：

```
值 = min_调度器响应  max_前缀  makespan(前缀) / OPT(前缀)
```

= "任意确定性在线算法竞争比 ≥ 值" 的真下界（自适应停止 = 前缀取 max）。
`--check tau` 只验证 值 ≥ tau，快几个量级，并输出违规状态集（证书雏形）。

## 生成者须知（LLM 读这里）

1. **结构合理即可，数值不必精确**：尺寸会交给 DE 优化，粗筛淘汰低值模板
2. **必须声明代数约束**：若正确性依赖某参数满足方程（如 α²−2α−2=0 锁定 α=1+√3），
   放进 `solve`。没有代数约束的"裸尺寸"模板几乎必然低于已知构造
3. **参考种子**：`seeds/fkt.json`（双层）、`seeds/braun_r1.json`（L/S 交替+几何级数+三次方程）、
   `seeds/rudin.json`（递推+夹逼+终止条件）；机制说明见仓库 `Mechanisms/MECHANISMS.md`
4. **已知陷阱**：
   - 层序错误 → 值暴跌（Rudin fwd 只有 5/3）
   - 无理参数种子不要用 `--check auto` 思想取 tau = 理论上界本身，留 ~1e-7 slack
   - 每层作业数通常是 m 或 m−1（层分离论证的前提）；终作业通常 = 2×最小层参数

## 种子模板已知值（回归测试基准）

| 种子 | 精确/阈值 | 期望 |
|---|---|---|
| fkt.json | 精确 | 1707/1000 = 1.707 |
| braun_r1.json | 精确 | = c1 ≈ 1.7310194（--check 用 1.7310194） |
| rudin.json (eps=0.01) | check | ≥ √3−eps，tau=1.7220508 PASS |
