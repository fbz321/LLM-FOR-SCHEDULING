# 模板池粗筛结果

漏斗阈值：coarse=1.70, fine=1.7320

| 状态 | 模板 | 文件 | 作业数 | 状态数 | 耗时 | 详情 |
|---|---|---|---|---|---|---|
| REJECTED | FKT_Perturbed_4x2 | qwen_20260817_123517_00.json | 13 | 14 | 0.0s | < 1.7000（14 状态） |
| L2-MATERIALIZE-FAIL | Rudin_Modified_Term | qwen_20260817_123517_01.json | None | None | 0.0s | 未定义的名字 'B' |
| L2-MATERIALIZE-FAIL | Braun_Geometric_Shift | qwen_20260817_123517_02.json | None | None | 0.0s | 作业尺寸必须为正: L0 = -0.85744771779340902084578436157678843047309505689663255890160 |
| KNOWN-BAND | FKT_Base_m4 | qwen_salv_00.json | 9 | 10 | 0.0s | >= 1.7000, < 1.7320（10 状态） |
| REJECTED | FKT_Perturb_a | qwen_salv_01.json | 9 | 10 | 0.0s | < 1.7000（10 状态） |
| L2-MATERIALIZE-FAIL | FKT_ThreeLayer | qwen_salv_02.json | None | None | 0.0s | 作业尺寸必须为正: a = -3.56155281280883027491070492798703851257359961268681021719933 |
| L2-MATERIALIZE-FAIL | Rudin_Sqrt3_Std | qwen_salv_03.json | None | None | 0.0s | 作业尺寸必须为正: B = -0.0249198421397214975121320630107836896005919950298154559201549 |
| L3-EVAL-ERROR | Rudin_Modified_M | qwen_salv_04.json | 9 | None | 0.0s | 非正作业尺寸 |
| L2-MATERIALIZE-FAIL | Rudin_B_Collapse | qwen_salv_05.json | None | None | 0.0s | 作业尺寸必须为正: where(i==n, S-A, A+2*A_next) = -0.43969262078590838405410927732473146993620813426446463309028 |
| L2-MATERIALIZE-FAIL | Rudin_Terminal_Scale | qwen_salv_06.json | None | None | 0.0s | 作业尺寸必须为正: B = -0.0249198421397214975121320630107836896005919950298154559201549 |
| L2-MATERIALIZE-FAIL | Braun_c1_Std | qwen_salv_07.json | None | None | 0.0s | 作业尺寸必须为正: L0 = -1.71774111746400409512872946295467783765963826857954252879681 |
| REJECTED | Braun_Geometric_Ratio | qwen_salv_08.json | 16 | 17 | 0.0s | < 1.7000（17 状态） |
| L2-MATERIALIZE-FAIL | Braun_Extended_Layers | qwen_salv_09.json | None | None | 0.0s | 作业尺寸必须为正: y = -2.00000000000000000000000000000221185190800602813513781129677 |
| L2-MATERIALIZE-FAIL | Braun_Reduced_Poly | qwen_salv_10.json | None | None | 0.0s | 作业尺寸必须为正: S0 = -2.75271672619682755489295787063924225506253162199189782023735E-31 |
| L2-MATERIALIZE-FAIL | Hybrid_FKT_Rudin | qwen_salv_11.json | None | None | 0.0s | 作业尺寸必须为正: B = -0.458333333333333333333333333333333333333333333333333333333333 |
| L2-MATERIALIZE-FAIL | Hybrid_Braun_Rudin | qwen_salv_12.json | None | None | 0.0s | 递推在 40 步内未终止 |
| L2-MATERIALIZE-FAIL | Novel_Asymmetric_4_3 | qwen_salv_13.json | None | None | 0.0s | 作业尺寸必须为正: y = 0E-59 |
| L2-MATERIALIZE-FAIL | Novel_Double_Final | qwen_salv_14.json | None | None | 0.0s | 作业尺寸必须为正: a = -1.99860691507845845109159302471798885920199886486157969992733E-30 |
| L2-MATERIALIZE-FAIL | FKT_Scaled_Final | qwen_salv_15.json | None | None | 0.0s | 作业尺寸必须为正: a = 0 |
| L2-MATERIALIZE-FAIL | Rudin_Init_Scale | qwen_salv_16.json | None | None | 0.0s | 作业尺寸必须为正: B = -0.0103133139937324349316357577749499561607949401663277223259859 |
| L2-MATERIALIZE-FAIL | Rudin_Modified_Term_r1 | repair_20260817_131237_00.json | None | None | 0.0s | 作业尺寸必须为正: where(i==n, 0, A_next) = 0 |
| L2-MATERIALIZE-FAIL | Braun_Geometric_Shift_r1 | repair_20260817_131237_01.json | None | None | 0.0s | 作业尺寸必须为正: L0 = -1.71774111746400409512872946295467783765963826857954252879681 |
| L2-MATERIALIZE-FAIL | FKT_ThreeLayer_r1 | repair_20260817_131237_02.json | None | None | 0.0s | 作业尺寸必须为正: d = -0.56066017177982128660126654315727355892725390653271105488251 |
| L2-MATERIALIZE-FAIL | Rudin_Sqrt3_Std_r1 | repair_20260817_131237_03.json | None | None | 0.0s | 作业尺寸必须为正: B = -0.0249198421397214975121320630107836896005919950298154559201549 |
| L2-MATERIALIZE-FAIL | Rudin_B_Collapse_r1 | repair_20260817_131237_04.json | None | None | 0.0s | 作业尺寸必须为正: B = -0.0249198421397214975121320630107836896005919950298154559201549 |
| L2-MATERIALIZE-FAIL | Rudin_Terminal_Scale_r1 | repair_20260817_131237_05.json | None | None | 0.0s | 作业尺寸必须为正: B = -0.0249198421397214975121320630107836896005919950298154559201549 |
| L2-MATERIALIZE-FAIL | Braun_c1_Std_r1 | repair_20260817_131237_06.json | None | None | 0.0s | 作业尺寸必须为正: L0 = -1.71774111746400409512872946295467783765963826857954252879750 |
| L3-EVAL-ERROR | Braun_Extended_Layers_r1 | repair_20260817_131237_07.json | 21 | None | 0.0s | 非正作业尺寸 |
| L2-MATERIALIZE-FAIL | Braun_Reduced_Poly_r1 | repair_20260817_131237_08.json | None | None | 0.0s | 作业尺寸必须为正: S0 = -1.29098448703577254402644692517983333590542329832322013853288E-31 |
| L2-MATERIALIZE-FAIL | Hybrid_FKT_Rudin_r1 | repair_20260817_131237_09.json | None | None | 0.0s | 作业尺寸必须为正: A = -8.3333333333333333333333333333333333333333333333333375E-11 |
| L2-MATERIALIZE-FAIL | Hybrid_Braun_Rudin_r1 | repair_20260817_131237_10.json | None | None | 0.0s | 作业尺寸必须为正: S0 = -25000000000000000000000000000000000000000000000000000000001 |
| REJECTED | Novel_Asymmetric_4_3_r1 | repair_20260817_131237_11.json | 15 | 16 | 0.0s | < 1.7000（16 状态） |
| L3-EVAL-ERROR | Novel_Double_Final_r1 | repair_20260817_131237_12.json | 14 | None | 0.0s | 非正作业尺寸 |
| L2-MATERIALIZE-FAIL | FKT_Scaled_Final_r1 | repair_20260817_131237_13.json | None | None | 0.0s | 牛顿法导数为零 (c=1.00000000000000000266476639373267851875533534047688202007139) |
| L2-MATERIALIZE-FAIL | Rudin_Init_Scale_r1 | repair_20260817_131237_14.json | None | None | 0.0s | 作业尺寸必须为正: where(i==n, S-A, A+2*A_next) = -0.0189356052693996410046392610244784772978162614015066698330895 |
