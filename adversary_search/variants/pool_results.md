# 模板池粗筛结果

漏斗阈值：coarse=1.70, fine=1.7320

| 状态 | 模板 | 文件 | 作业数 | 状态数 | 耗时 | 详情 |
|---|---|---|---|---|---|---|
| L1-INVALID | broken syntax test | broken_syntax.json | None | None | 0.0s | layers[0].emit[0].size: 表达式语法错误 '2*a +': invalid syntax (<unknown>, line 1) |
| REJECTED | FKT bad sizes (a=0.4, b=0.6) | fkt_bad.json | 9 | 10 | 0.0s | < 1.7000（10 状态） |
| REJECTED | FKT perturbed (a=0.22) | fkt_perturbed.json | 9 | 12 | 0.0s | < 1.7000（12 状态） |
| L2-MATERIALIZE-FAIL | negative size test | negative_size.json | None | None | 0.0s | 作业尺寸必须为正: b = -0.5 |
| KNOWN-BAND | Rudin deep (eps=0.001) | rudin_deep.json | 25 | 26 | 0.1s | >= 1.7000, < 1.7320（26 状态） |
| KNOWN-BAND | Rudin deeper (eps=0.0001) | rudin_deeper.json | 33 | 34 | 1.9s | >= 1.7000, < 1.7320（34 状态） |
| REJECTED | three-layer probe (4a+4b+4c+1) | three_layer.json | 13 | 14 | 0.0s | < 1.7000（14 状态） |
