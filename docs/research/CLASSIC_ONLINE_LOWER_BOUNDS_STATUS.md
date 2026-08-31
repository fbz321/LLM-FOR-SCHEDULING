# 经典在线同型机 Makespan 下界现状

> 最后核对：2026-08-31  
> 模型：确定性、非抢占、立即且不可撤销分配的
> `P | online, list | Cmax`。

## 1. 模型与证据边界

作业逐个到达，算法只在作业到达时得知其大小，并必须立即将其分配到
`m` 台相同机器之一。竞争比以同一完整作业集合的真正离线最优 makespan
`OPT` 为分母。

本文主表不包含：

- 随机化算法；
- 已知总工作量（Known Sum）等半在线模型；
- 允许缓冲、重排、迁移、抢占或拒绝作业的模型；
- 相关机/不相关机；
- 只用 `max(max job, total/m)` 代替真正 `OPT` 的 pseudo lower bound；
- Lean 文件中的公理占位结果。

还必须区分三类证据：

1. 文献已经证明的真实下界；
2. 本仓库独立计算或形式化复核的部分；
3. 尚未完成的实验、部分缓存或弱 `OPT` 分母结果。

## 2. 总体结论

令 `R_m*` 为 `m` 台机器上最佳确定性在线算法的最优竞争比。小机器数中：

```text
R_2* = 3/2
R_3* = 5/3
sqrt(3) <= R_4* <= 26/15
```

因此 `m=2,3` 已解决；`m=4` 尚有

```text
26/15 - sqrt(3) ~= 0.001282526
```

的缺口。

渐近情形当前采用的文献区间为：

```text
1.88 <= R_infinity <= 1.9201...
```

下界来自 Rudin--Chandrasekaran 的 layering adversary，上界来自
Fleischer--Wahl 的在线算法。这一缺口自 2003 年以来仍未闭合。

## 3. 按机器数列出的真实下界

下表中的 `m>=5` 数字是 Rudin--Chandrasekaran 文献所列的显式构造值。
没有列出的机器数不能通过相邻行插值得到结论。

| 机器数 `m` | 文献下界 | 状态/说明 |
|---:|---:|---|
| 2 | `3/2 = 1.5` | 与上界相等，已解决 |
| 3 | `5/3 = 1.666666...` | 与上界相等，已解决 |
| 4 | `sqrt(3) = 1.732050807568...` | 任意 `epsilon>0` 有有限的 `sqrt(3)-epsilon` 构造 |
| 5 | `1.74833497030641` | Rudin Table A2 |
| 6 | `1.77409792411` | Rudin Table A3 |
| 7 | `1.792667559` | Rudin Table A4 |
| 8 | `1.803471135` | Rudin Table A5 |
| 9 | `1.80896128` | Rudin Table A6 |
| 10 | `1.81432683354` | Rudin Table A7 |
| 12 | `1.8252768572641` | Rudin Table A8 |
| 13 | `1.829976395118` | Rudin Table A9 |
| 14 | `1.83679075816032` | Rudin Table A10 |
| 15 | `1.83933479388067` | Rudin Table A11 |
| 16 | `1.84299410215536` | Rudin Table A12 |
| 18 | `1.84548114842048` | Rudin Table A13 |
| 24 | `1.85669916563964` | Rudin Table A14 |
| 120 | `1.875` | Rudin Table A15 |
| 3600 | `1.88` | Rudin Table A16 / 渐近代表构造 |

早期统一基准是 Faigle--Kern--Turán 对所有 `m>=4` 的自适应下界：

```text
1 + sqrt(2)/2 = 1.70710678118...
```

Rudin 的 layering 方法通过 Type-1、Type-2、Type-3 层和最终强制作业，
将固定 `m` 的界逐步提高，并在大机器数达到 `1.88`。

## 4. 代表性上下界

| `m` | 下界 | 上界 | 当前缺口 |
|---:|---:|---:|---:|
| 2 | `3/2` | `3/2` | `0` |
| 3 | `5/3` | `5/3` | `0` |
| 4 | `sqrt(3)` | `26/15` | `~0.001282526` |
| 5 | `1.74833497030641` | `85/48 = 1.770833...` | `~0.02249836` |
| 6 | `1.77409792411` | `9/5 = 1.8` | `~0.02590208` |
| 7 | `1.792667559` | 文献表中约 `1.8229` | `~0.0302` |
| 渐近 | `1.88` | `~1.9201` | `~0.0401` |

这里 `85/48`、`9/5` 在本表是**算法上界**。仓库另有同样数值作为
“pseudo lower bound”出现；后者只针对弱分母，不能作为真实竞争比下界。

Graham List Scheduling 的

```text
2 - 1/m
```

也是该特定算法的紧上界，不是所有在线算法的通用下界。

## 5. 主要发展路线

### 5.1 Graham 基准

List Scheduling 满足 `(2-1/m) OPT`。它建立了经典算法基准，但其紧例只
证明 List Scheduling 本身的局限，不自动给出所有在线算法的下界。

### 5.2 Faigle--Kern--Turán（1989）

使用简洁的自适应两层对抗器，对所有 `m>=4` 得到
`1+sqrt(2)/2 ~= 1.7071`。这是后续分层构造的重要起点。

### 5.3 1990 年代的小 `m` 改进

Chen--van Vliet--Woeginger 等工作推进了固定小机器数的上下界，尤其是
`m=4` 的约 `1.7310` 下界和 `26/15` 上界。Rudin 随后把 `m=4` 下界推到
`sqrt(3)` 的极限形式。

### 5.4 Rudin--Chandrasekaran（2003）

layering adversary 维护层间进度量，并同时给每个关键前缀建立离线打包
上界。其贡献包括：

- `m=4` 的 `sqrt(3)-epsilon` 构造；
- `m=5,6,...` 的一系列显式下界；
- 渐近下界 `1.88`。

### 5.5 Braun--Chung--Graham（2025）

对 `m=4` 给出更细的自适应加性下界，例如

```text
C_ALG >= sqrt(3) OPT - (2 - sqrt(3)).
```

它加强了有限尺度/加性证书，但没有把主乘法竞争比推进到 `sqrt(3)` 以上。
自适应对抗器也不能误写成“一条固定序列同时击败所有算法”。

## 6. 本仓库的独立复核状态

| `m`/构造 | 文献值 | 本仓库严格复核 | 状态 |
|---|---:|---:|---|
| 2 | `3/2` | `3/2` | 已通过小型精确博弈复现 |
| 3 | `5/3` | Lean 当前仅形式化较弱的 `3/2` | 文献成立；项目覆盖不完整 |
| 4 FKT | `1+sqrt(2)/2` | 约 `1.7071` | 已复核/形式化 |
| 4 Rudin | `sqrt(3)` 极限 | 若干 `sqrt(3)-epsilon` 有限实例 | 文献一般性结论强于计算实例 |
| 4 Braun--Chung--Graham | 加性 `sqrt(3)` 结构 | 有对应 Lean 实现 | 不突破乘法 `sqrt(3)` |
| 5 Rudin | `1.74833497030641` | `1.748334` | 71 作业公开转录 PASS |
| 6 Rudin | `1.77409792411` | 仅完成 81/91 个 prefix OPT | PARTIAL，项目无最终结论 |
| 7 Rudin | `1.792667559` | `1.7926675` | 57 作业公开转录 PASS |
| 8 及更大 Rudin 构造 | 见主表 | 未逐一完成 exact-prefix 博弈 | 目前主要依赖文献证明 |

`m=5` 的复核精度低于文献显示值，是因为公开 Table A2 只有打印小数，
没有原电子表格的 guard digits。本项目不能把元数据中的文献值当成由公开
整数序列重新证明的精度。

固定序列复核详情见：

- [`adversary_search/RUDIN2001_RESULTS.md`](../../adversary_search/RUDIN2001_RESULTS.md)
- [`adversary_search/results/m5_structured/README.md`](../../adversary_search/results/m5_structured/README.md)

## 7. 不应计入真实下界的结果

### 7.1 Pseudo lower bounds

仓库中可见：

```text
m=4: 26/15
m=5: 85/48
m=6: 9/5
```

作为 pseudo lower bound 的版本只证明相对于
`max(max job, ceil(total/m))` 等弱分母的比值，不证明相对于真正 `OPT` 的
同样比值。它们不能代替 Rudin 的真实下界。

### 7.2 模型变体

Known Sum、bin stretching、grade of service、decreasing arrivals 等有各自的
下界，但问题定义不同，应单独汇报。仓库的部分 Known Sum 小 `m` 公式还是
公理占位并存在文档数值冲突，不应引用为核心模型成果。

### 7.3 仓库陈旧数值

`OnlineScheduling/Main.lean` 的展示文本曾写渐近下界约 `1.8520`，与主
README、`Rudin.lean` 和 Rudin 文献的 `1.88` 冲突。后续查看应采用 `1.88`，
并把 `1.8520` 视为旧下界/陈旧展示，而非当前最好结果。

## 8. 当前研究判断

目前没有证据表明在 Rudin tableau 周围继续做局部倍率、顺序或复制手术能
产生普遍的新界。本项目已在 `m=5` 上严格排除大量这类有限邻域，但这些负
结果不能外推为“不存在更好构造”。

更有希望的方向是：

1. 搜索依赖当前负载状态的自适应对抗树，而非先固定 Rudin 风格序列；
2. 改变层内重数模式，如 `3+2`、`3+1+1` 或更多混合尺寸；
3. 从 exact OPT 的反复打包中提取不属于既有 tableau 的新恒等式；
4. 联合移除多个临界前缀，而不是只优化后缀；
5. 面向大 `m` 设计可扩展组合结构，直接攻击 `[1.88,1.9201]` 缺口。

## 9. 主要来源

- John F. Rudin III and R. Chandrasekaran,
  [“Improved Bounds for the Online Scheduling Problem,” SIAM Journal on Computing 32(3), 717--735 (2003)](https://epubs.siam.org/doi/10.1137/S0097539701393258).
- [DBLP bibliographic record for Rudin--Chandrasekaran](https://dblp.org/rec/journals/siamcomp/RudinC03).
- Rudolf Fleischer and Michaela Wahl,
  [“On-line Scheduling Revisited,” Journal of Scheduling 3(6), 343--353 (2000)](https://doi.org/10.1002/1099-1425(200011/12)3:6%3C343::AID-JOS49%3E3.0.CO;2-7).
- R. L. Graham,
  [“Bounds for Certain Multiprocessing Anomalies” (1966)](https://doi.org/10.1002/j.1538-7305.1966.tb01709.x).

## 10. 一句话结论

> 经典确定性在线同型机 makespan 调度在 `m=2,3` 已解决；`m=4` 位于
> `[sqrt(3),26/15]`；Rudin--Chandrasekaran 给出从 `m=5` 的
> `1.74833497030641` 逐步增长到渐近 `1.88` 的最好已知下界系列，而最好
> 已知渐近上界约为 `1.9201`。本项目复核了其中若干固定序列，但尚未产生
> 超过文献的新真实下界。
