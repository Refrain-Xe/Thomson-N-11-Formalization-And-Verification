# Thomson 问题 N = 11：精确三点 SDP 界、松弛间隙诊断与 Lean 4 形式化证明

本仓库是「11 个电子在单位球面上库仑能量最小构型」（Thomson 问题 $N = 11$）的严格数值分析、精确有理半定规划（SDP）下界与 Lean 4 内核形式化证明仓库。

## 1. 已证定理（Lean 4 内核形式化，零 `sorry`、零 `native_decide`、仅依赖标准三公理）

设 $S^2 \subset \mathbb{R}^3$ 为单位球面，$x = (x_0, \dots, x_{10}) \in \mathrm{SphereConfig}(11)$ 为球面上两两不同的 11 个点，库仑（Riesz $s = 1$）能量为
$$E(x) = \sum_{0 \le i < j < 11} \frac{1}{\|x_i - x_j\|}.$$

冻结挑战文件 `formal/lean/ComparatorChallenges/ThomsonN11.lean` 中的两条里程碑定理，以及本轮推进的加强全局三点 SDP 下界与精确有理 $C_{2v}$ 构型上界，已在 `formal/lean/ThomsonN11/Solution.lean` 中全部完成 Lean 4 内核形式化证明（公理白名单：`[propext, Classical.choice, Quot.sound]`）：

| 定理（`namespace ThomsonN11`） | 严格形式化陈述 | 数值含义与证明方法 |
| --- | --- | --- |
| `thomson_eleven_M0` | `∀ x ∈ SphereConfig 11, (55 / 2 : ℝ) ≤ coulombEnergy x` | 里程碑 M0（`27.5`，直径界 $\|x_i - x_j\| \le 2$） |
| `thomson_eleven_M1` | `∀ x ∈ SphereConfig 11, (155 / 4 : ℝ) ≤ coulombEnergy x` | 里程碑 M1（`38.75`）：显式二次次估 $f(t)=\frac{7}{10}+\frac{2}{5}t+\frac{7}{40}t^2$ + 六平方 Lukács 恒等式 + 一/二阶球谐矩，实证下界 `583/15 = 38.8666… > 38.75` |
| `thomson_eleven_sdp_M10` | `∀ x ∈ SphereConfig 11, (2027773585218537 / 50000000000000 : ℝ) ≤ coulombEnergy x` | **加强全局三点 SDP 下界**（`40.55547170437074`）：$(M,K)=(10,10)$ $S_3$ 对称约化 Bachoc–Vallentin / Cohn–Woo 三点半定规划证书 + 纯整数 Cholesky + 19 片并行 2D-Kronecker 内核验证 |
| `thomson_eleven_upper_bound` | `∃ x ∈ SphereConfig 11, coulombEnergy x ≤ (2029822525409531 / 50000000000000 : ℝ)` | **精确有理 $C_{2v}$ 构型上界**（`40.59645050819062`）：5 参数有理球极投影构造严格在 $S^2$ 上的 $C_{2v}$ 构型 `c2vWitness`，距数值最优值仅 $1.46 \times 10^{-14}$ |
| `thomson_eleven_bounds_sandwich` | 双边夹逼合取定理 | 将 $E_1(11)$ 严格锁定在长度 `0.04097880381988` 的有理区间 `[40.55547170437074, 40.59645050819062]` 内 |

## 2. 核心科学发现：$N = 11$ 三点 SDP 松弛的本征正间隙（$\Delta \approx 0.0395$）

在 80-dps `mpmath` 高精度诊断（`numerics/bounds/phase0_candidate.py`）与 200/224-bit `SDPA-GMP` 纯有理证书扫阶（`numerics/bounds/sym_cap_sdpa.py`、`sym_strip_sdpa.py`、`phase0_gap_diagnosis.py`）中，我们定位并定量刻画了 $N = 11$ 与 $N = 7, 8, 9$ 的本质数学分水岭：

1. **80-dps $C_{2v}$ 驻点刻画**：5 参数有理球极投影子流形上的牛顿法将边收缩二十面体 $X^*_{11}$（轨道分解 $1+2+2+2+4$）收敛至 $\|\nabla_{S^2} E\|_\infty = 8.52 \times 10^{-81}$，
   $$E^*(11) = 40.59645050819060538663553135833447301835336406781920\dots,$$
   完整 $22\times 22$ 黎曼 Hessian 恰有 3 个 $\mathfrak{so}(3)$ 零模（$\sim 10^{-80}$）与 19 个严格正特征值（$\lambda_{\min}(H_0) = 0.090673217656\dots > 0$）；55 个点对分裂为 **20 个不同内积轨道**，最小内积 $m^* = -0.9990227934594476\dots$（重数 2，两对不相交近对跖点），相邻能级最小间隔 $g_{\min} = 0.0036973115\dots$。次低局部极小（$C_{5v}$ 去顶二十面体）能量为 $40.615117336946\dots$（高 $+0.0186668$）。
2. **三点 SDP 阶梯收敛实测**：全局无截断（$a_0 = -1$）$S_3$ 三点 SDP 严格有理认证下界在 $M = K \in [6, 12]$ 上逼近本征松弛极限：
   - $(6,6): 40.533315701817$（$\Delta = 0.063135$）
   - $(7,7): 40.545314785703$（$\Delta = 0.051136$）
   - $(8,8): 40.551494289332$（$\Delta = 0.044956$）
   - $(9,9): 40.554160636831$（$\Delta = 0.042290$）
   - $(10,10): 40.555471704371$（$\Delta = 0.040979$，已入 Lean 4 内核定理 `thomson_eleven_sdp_M10`）
   - **$(12,12): 40.556960329409$**（$\Delta = 0.039490$，Stage A 最强全局严格三点 SDP 证书 `n11-symcap-n11_am1_M12_K12.json`；在 $(12,12)$ 下奇阶谐波块 $F_9, F_{11} \sim 10^{-20}\dots 10^{-23}$ 失活，偶阶二十面体谐波块 $F_{10} = 1.05\times 10^{-4}$ 激活，但仅再推进 $+0.001489$）。
   即使加入近对跖截断 $a_0 = -1023/1024 < m^*$（$(10,10) \to 40.55553958$，$(12,12) \to 40.556970864736$，间隙仍为 $0.039480$）、上界截断 $b_0 = 53/100$、大幅抬高帽阈值 $a_0 = -9/10$（$(8,8) \to 40.58493495 < E^*(11)$，而真实几何约束极小已达 $40.63245$），或切换 $(2,9)$ typed 极环条带 SDP（`[-9991/10000, -999/1000]` 在 $(7,7)$ 下为 $40.54800350$），松弛间隙依然顽固维持在 $\approx 0.0395$。
3. **几何根因（分数二十面体伪矩测度）与四点 SDP 层级实测（`phase0_gap_diagnosis.py`、`phase0_4pt_probe.py`）**：
   - 在固定 $X^*_{11}$ 真矩上的 1D 多项式次估 LP 在 $M=8$（$\deg H = 14$）时已达 `40.59645010`（间隙仅 $4.04 \times 10^{-7}$），证明瓶颈并非多项式逼近阶数，而是三点半定矩条件本身存在更低能量的**虚假三点伪矩**：$(10,10)$ 对偶最优 9 节点 Gauss–Christoffel 测度在 $t \approx -0.99964$ 处放置了 **$3.395$ 对分数对跖点**（同时在 $t \approx \mp 1/\sqrt{5}$ 附近放置 $18.01$ 与 $21.87$ 对二十面体邻接点对）。
   - 在真实 $\mathbb{R}^3$ 球面几何中，含 $k$ 对精确对跖点的 11 点最小能量分别为 $k=1: 40.59691$、$k=2: 40.59768$、$k=3: 40.62578$、$k=4: 40.78043$、$k=5: 40.90067$——$k=1,2$ 能量极接近 $E^*(11)$ 阻断了近对跖单对条带排除，而三点 SDP 缺少四点 Gram 秩 3 约束（$\det G_4 = 0$），将 12 顶点正二十面体缺失 1 个顶点的拓扑缺陷弥散为约 $3.4$ 对分数对跖点而无需支付三维嵌入的 $+0.03\sim+0.18$ 几何受挫代价。
   - **四点 SDP 层级实测**：构造完整的 $S_{11}\times O(3)$ 约化耦合三点+四点 SDP（含 $\det G_4 = 0$ 理想乘子、4 点 Putinar/面行列式 SOS、Binet–Cauchy 叉积块 `Harm4_odd`、对旗块 `Flag2_even` 及 $(\mathbb{R}^3)^{\otimes d}$ 全局点对张量块 `GlobNat`/`GlobAx`），在同多项式次数下严格提升三点界（$D=6, M=4$: `40.32802558 -> 40.49109850`，**`+0.16307292`**；$D=8, M=5$: `40.50635763 -> 40.51417969`，**`+0.00782206`**）。但低阶四点（$D_4 \le 8$，天花板 `40.51418`）尚不足以分辨 9 个支撑节点，因此把 $D_4 = 4, 6$ 耦合到高阶三点 $(M=8, D_3=14, 40.55149429)$ 增益为 `0`（`< 2e-13`）——证实要借四点 SDP 击穿 `~40.557` 天花板必须推进至高阶四点（$D_4 \ge 14\text{--}18$）或联合多对分支定界。

## 3. 一键复现与验收标准

### 3.1 数值与精确有理 SDP 证书验收（Stage A）
```bash
python3 numerics/optimize.py
python3 numerics/optimize.py --selftest
python3 numerics/bounds/sym_cap_sdpa.py --selftest
python3 numerics/bounds/sym_strip_sdpa.py --selftest
python3 numerics/bounds/verify_all.py
```
`verify_all.py` 独立复验 80-dps $C_{2v}$ 驻点、有理上界见证、`certificates/*.json` 全部 **15 张精确有理证书**（13 张 `symcap` 全局/截断证书 + 2 张 `symstrip` $(2,9)$ 极环条带证书，共 **410 个半正定块**的精确整数 Bareiss Sylvester 主子式正定检验、1D Lukács 恒等式与三点/`(2,9)` 组合恒等式误差 `0`）、Stage A 诊断账本一致性（`phase0_sdp_sweep.json`、`phase0_gap_diagnosis.json`、`phase0_4pt_probe.json`）、21 组球面有理构型对偶估值及 **6 项篡改负对照（NC1–NC6）**。

### 3.2 Lean 4 形式化证明验收（Stage B）
本机工具链固定为 `leanprover/lean4:v4.34.1`（位于 `~/.elan/bin`），Mathlib 固定为 `d13f23b723b8a846827a245b89c10fc7d3f11612`（严禁运行 `lake update`）：
```bash
export PATH="$HOME/.elan/bin:$PATH"
bash formal/lean/scripts/check.sh
bash formal/lean/scripts/negative-control.sh
```
`check.sh` 依次验证：(1) `SHA256SUMS.txt` 全文件哈希锁定（同时覆盖工作树磁盘文件与 git 跟踪列表）；(2) 基础定义块逐字一致；(3) 全模块感知字符串字面量的去注释禁用记号扫描（零 `sorry`、`native_decide`、`ofReduceBool`、`skipKernelTC` 等）；(3b) 仓库字节码与构建产物卫生；(4–5) `lake build ThomsonN11 ComparatorChallenges`（挑战文件恰 2 处预期 `sorry`，解法模块 0 处）；(6) `#print axioms` 严格三公理白名单（覆盖全部 5 条顶层定理）；(7) `compare_statements.py` 10/10 挑战常量零豁免比对。`negative-control.sh` 运行语句翻转（NC1）、内核证书篡改（NC2）与字符串伪注释偷渡禁用项拦截（NC3）三项负对照。

## 4. 仓库结构

    thomson-n11/
    ├── README.md                              项目总览、已证定理与科学结论
    ├── PROGRESS.md                            按轮次顺序追加的完整研发与验收日志
    ├── notes/strategy.md                      技术架构、三点 SDP 间隙根因分析与四点实测路线图
    ├── certificates/                          15 张精确有理 SDP 证书（13 张 symcap + 2 张 symstrip）
    ├── numerics/
    │   ├── energy.py / optimize.py            多起点球面优化与参考能量勘误自测门
    │   └── bounds/
    │       ├── exact_linalg.py                精确整数 Bareiss Sylvester 正定检验、LDL^T 与 SDPA 解析
    │       ├── sym_cap_sdpa.py                纯有理 S3 同型约化三点 SDP 引擎（支持任意 K <= M 与上下截断）
    │       ├── sym_strip_sdpa.py              纯有理 (2, n-2) typed 极环条带三点 SDP 引擎与精确证书校验
    │       ├── phase0_candidate.py            80-dps C2v 球极投影牛顿求解与 22x22 黎曼 Hessian 谱诊断
    │       ├── phase0_sdp_sweep.py            S3 / (2,9) 三点 SDP 证书汇总与在线扫描脚本
    │       ├── phase0_gap_diagnosis.py        对偶伪矩谱、1D 真矩 LP 与 k-对跖真构型能量阶梯独立诊断
    │       ├── phase0_4pt_probe.py            S_11 x O(3) 约化耦合四点 SDP 层级（det G_4=0 + 张量块）实测探针
    │       ├── export_lean_sdp.py             导出零 Mathlib 依赖的纯整数 Cholesky + 19 片 Kronecker 证书
    │       ├── export_lean_upper.py           导出纯整数射影球极投影 C2v 上界见证 UpperBound.lean
    │       ├── verify_all.py                  Stage A 全量进程外复验与 6 项负对照总门
    │       └── results/                       JSON 诊断与复验账本（phase0_*.json, verify_all.json）
    └── formal/lean/                           Lean 4 包 ThomsonN11（Mathlib d13f23b）
        ├── SHA256SUMS.txt                     全包冻结哈希清单（pin_hashes.sh 生成）
        ├── ComparatorChallenges/ThomsonN11.lean  绝对冻结挑战声明（M0 = 55/2, M1 = 155/4）
        ├── ThomsonN11/Solution.lean           M0, M1, thomson_eleven_sdp_M10, thomson_eleven_upper_bound 总装
        ├── ThomsonN11/StageB/                 ThreePoint, PolyKronDefs, PolyKron, PolyKronFast, SdpCert*, UpperBound
        └── scripts/                           check.sh, negative-control.sh, CheckAxioms.lean, compare_statements.py, pin_hashes.sh

## 5. 开源协议（License）

Licensed under the [Apache License, Version 2.0](LICENSE) (Copyright 2026 Yang Li).
