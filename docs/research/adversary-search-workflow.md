# m=4 自适应对抗搜索工作流（AI 辅助）

> 目标：在 4 台相同机器的确定性在线 makespan 模型中，寻找严格超过 `sqrt(3)` 的有限自适应策略；目标区间为 `sqrt(3) < rho <= 26/15`。本文件描述方法，不把启发式结果或有限负搜索写成定理。
>
> 当前经典上下界、证据等级和项目复核状态见 [`CLASSIC_ONLINE_LOWER_BOUNDS_STATUS.md`](CLASSIC_ONLINE_LOWER_BOUNDS_STATUS.md)。

## 0. 模型、量词与规范化

- 作业必须立即、不可撤销地分配；调度器响应后，对抗者才能选择下一作业。
- 整体缩放不改变竞争比。建议固定第一件正作业为 `1`，允许后续作业大于 `1`；不要把未知未来最大作业强制限制为 `1`。
- 探索阶段可以使用有限有理动作集 `G`，但“没有策略”只对该 `G` 和给定深度成立。连续动作模型需要额外的结构定理。
- 规范状态至少包含：

```text
(m, sorted machine loads, sorted exact job multiset, remaining depth, action-menu id)
```

  对整数状态可再除以所有 loads/jobs 的 gcd；只有在转移和 OPT 语义保持不变时才能合并缩放状态。
- 固定序列与自适应策略必须分开：固定序列要求同一序列对所有调度器响应成立；自适应策略是状态到下一作业/停止的映射。

## 1. 阈值 OR–AND 搜索

目标是判断给定有理阈值 `tau` 是否可达，而不是优先计算完整 minimax 分数：

```python
def winning(state, tau):
    key = canonical_key(state, tau)
    if key in memo:
        return memo[key]

    if makespan(state.loads) * tau.denominator >= \
            tau.numerator * exact_opt(state.jobs):
        memo[key] = True
        return True
    if state.remaining == 0:
        memo[key] = False
        return False

    for p in ordered_actions(state):                 # adversary: OR
        children = distinct_scheduler_children(state, p)
        if all(winning(child, tau) for child in children):  # scheduler: AND
            policy[key] = p
            memo[key] = True
            return True

    memo[key] = False
    return False
```

- 达到阈值即可停止；调度器找到一条逃逸边即可使当前作业失败。
- `canonical_key` 必须包含完整作业多重集；不能只用 `loads`，因为相同负载可能来自不同历史并有不同 OPT。
- `tau` 在一次搜索中固定时可作为 run metadata，而不是每个 key 的字段；不同阈值的缓存不得混用。
- 对称性只删除相同负载值的机器响应。未经证明不得使用 majorization 或“负载逐坐标支配”剪枝。
- 可选用 proof-number search、AO* 或 alpha-beta，但剪枝必须保留 OR–AND 量词语义。

## 2. Exact OPT 服务

OPT 是独立的、内容寻址的服务，而不是递归中任意近似函数：

```text
key = (m, sorted exact job multiset)
value = exact OPT + method + optional packing witness
```

分层实现：

1. `LB = max(largest job, ceil(total/m), stronger safe bounds)`，并用 LPT 或其他构造给上界；若上下界相等，直接返回。
2. 对容量 `C` 做精确 bin-feasibility decision，在上下界间二分；利用相同作业/机器对称、subset-sum 或 meet-in-the-middle。
3. 仅对前两层无法解决的前缀运行 branch-and-bound。

缓存应绑定精确多重集，支持原子写入、失败恢复和单 key in-flight 去重。下界只能用于安全排除：若用 `LB <= OPT` 的分母证明调度器存在低于 `tau` 的逃逸，该候选可拒绝；用 LB 得到的“对抗者 PASS”必须标记为 unresolved，不能作为真实下界。

## 3. 搜索阶段与动作生成

不要从 `N=20` 直接扩大到 `N=100` 并进行全网格深搜。推荐漏斗：

### Stage A：校准

- `m=2` 精确复现 `3/2`；
- `m=4` 复现 FKT 的约 `1.707`；
- 以 Rudin 参数作为 seed，检查 `sqrt(3)-epsilon`，不要求有限深度恰好达到 `sqrt(3)`。

### Stage B：启发式发现

使用 beam、MCTS、double-oracle 或 LLM 产生候选动作。所有估值输入完整历史特征（loads、job multiset、OPT/packing 摘要、深度）；启发式不能合并语义不同的状态，也不能承担证明。

### Stage C：状态相关动作集

每个状态先生成少量有理候选：

- 使 `load_i + p` 接近 `tau * D` 的临界尺寸；
- 现有尺寸、尺寸差、`OPT - load_i` 等结构关系；
- 已知 packing 的余量和整数/有理关系；
- 上轮策略动作附近的有理扰动。

采用 progressive widening：瓶颈状态才扩大动作集。动作菜单、顺序、随机种子和候选生成规则必须写入 manifest。

### Stage D：CEGIS / escape-guided refinement

1. 在当前有限动作集搜索候选策略；
2. 独立 checker 找最弱 scheduler escape；
3. 从该状态的 loads、packing 和阈值余量提取封堵所需的临界动作；
4. 将动作加入菜单并重跑；
5. 直到获得完整证书、预算耗尽或证明当前有限菜单无解。

## 4. 证书策略 DAG

正结果保存 canonical DAG，而不是只保存一条路径或庞大树：

```json
{
  "schema_version": 1,
  "m": 4,
  "tau": "17321/10000",
  "root": "state-hash",
  "states": {
    "state-hash": {
      "loads": ["..."],
      "jobs": ["..."],
      "remaining": 12,
      "action": "...",
      "responses": {"load-class-0": "child-hash"}
    }
  }
}
```

独立 checker 必须确认：root、每个正有理作业、所有不等价响应、状态转移、最大深度、DAG 无非法循环，以及每个前缀的 exact OPT 或可独立验证的 packing/OPT 证书。成功时输出一条完整 winning policy；失败时保存 scheduler escape witness 和 unresolved 原因。

## 5. 证据等级和负结果

统一使用以下标签：

```text
heuristic candidate
exact restricted-game PASS
independent finite-policy certificate
parameterized mathematical theorem
Lean-kernel theorem
```

- `exact restricted-game PASS` 只说明指定动作集/深度中的策略通过。
- 有限动作集或有限深度无解，只能说明该受限搜索空间无解。
- 启发式“最好值”、MCTS 估值和局部网格负结果不能写成结构族全局最优或连续模型不可能。
- `fictitious play` 的经验最佳响应可能循环；其混合策略收敛结论不等于纯自适应策略证书。因此只用于发现，不能假定收敛到所需鞍点。
- 固定序列的最佳响应不能替代 state-dependent adversary。

## 6. 结构提炼与 Lean 交接

对 winning DAG 自动提取：尺寸重数、层/深度、紧前缀、调度器分支、exact OPT、packing witness、近等式和尺寸比。再进行 rational reconstruction、PSLQ 和 packing signature 聚类。LLM 只阅读这些结构化摘要，提出参数族和证明分解，不直接从原始日志猜公式。

Lean 交接顺序：

1. 先独立重放有限策略 DAG；
2. 再证明 packing、强制响应和终止性；
3. 最后抽象为参数族/`forall epsilon` 命题。

## 7. 验收与复现

一次可发布的突破必须同时满足：

- `tau > sqrt(3)` 且为严格有理比较；
- 全部策略分支通过独立 checker；
- 每个 OPT 由独立 exact solver 或可检查 packing 证书确认；
- clean-cache 重放结果一致；
- manifest 记录代码版本/哈希、动作菜单、深度、随机种子、缓存统计和证据等级；
- 通过 `lake build` 与 axiom/sorry 审计后，才可声称 Lean 结果。

对文献方法的借鉴（如 request-answer game、best-response dynamics）应标为方法启发；若主要依据摘要或索引而未核对原论文/程序细节，不应把其数值或完备性表述为已验证事实。
