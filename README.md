# Thomson 问题 N = 11：证明工程仓库（奠基阶段）

本仓库是「11 个电子在单位球面上库仑能量最小构型」这一开放问题的严格证明工程的工作仓库。
当前为**奠基阶段**：仓库骨架、数值复现、Lean 挑战命题已就位；证明本身（Lean）属于后续运行。

## 1. 定理陈述

设 `S² ⊂ ℝ³` 为单位球面，`x = (x₁, …, x₁₁)` 是球面上两两不同的 11 个点，其库仑（Riesz s = 1）能量为

    E(x) = Σ_{1 ≤ i < j ≤ 11} 1 / ‖xᵢ − xⱼ‖   （弦距离的倒数）。

**目标定理（最终形态见 `notes/strategy.md`，尚未进入 Lean）**：E 在 11 点构型集合上取得最小值
`E₁(11) = 40.596450508…`，且最小化构型在相差一个 `O(3)` 正交变换与点的重排下唯一（数值上为
C2v 对称的「边收缩二十面体」）。唯一性的严格表述以及最优构型的隐式刻画（仿 KLT 论文对方反棱柱
高度的处理）将随攻坚推进写入 `formal/lean/ComparatorChallenges/ThomsonN11.lean`。

**已固定的 Lean 挑战命题**（`formal/lean/ComparatorChallenges/ThomsonN11.lean`，全部以 `sorry` 结尾）：

| 命题 | 陈述 | 含义 |
| --- | --- | --- |
| `thomson_eleven_M0` | `∀ x ∈ SphereConfig 11, (55/2 : ℝ) ≤ coulombEnergy x` | 里程碑 M0：弱有理下界 27.5，任何严肃方法（两点/Yudin 型界）都应先拿下 |
| `thomson_eleven_M1` | `∀ x ∈ SphereConfig 11, (155/4 : ℝ) ≤ coulombEnergy x` | 里程碑 M1：有理下界 38.75，距真实最小值约 1.85，计划由三点 SDP 方法拿下 |

基础定义 `R3`、`SphereConfig`、`coulombEnergy`、`cyl` 从参考仓库
`references/thomson-n7-lean` 逐字搬运（仅改命名空间），保证与 N = 7 已验证工程使用同一套表述。

## 2. 猜测最优构型与参考能量

**参考能量（勘误后）**：

    E₁(11) = 40.596450508…

**勘误说明（重要）**：本项目的任务书原先钉的参考能量是 39.783856229。该数值**低于真实全局最小值，
不可达**，也不出现在任何已发表的 Thomson 能量表中。经三重独立证据裁定改钉为 40.596450508（容差
1e-5），勘误过程与证据全文见 `PROGRESS.md` 第 3 节；要点：

1. 本仓库 `numerics/optimize.py` 的多起点搜索（60 个随机起点 + 生长策略 + basin-hopping +
   结构族扫描）全部收敛到 E = 40.59645050819059，切向梯度 ~1e-10；
2. 同一代码在 N = 7/8/9/10/12 上逐一复现文献值（误差 ≤ 1e-9），方法可信；
3. Wikipedia《Thomson problem》表列出 N = 11 → U = 40.596450510（C2v，"edge-contracted
   icosahedron"）；Wales–Ulker Cambridge Cluster Database 表列出 40.5964505，且其坐标文件
   （`xyz/11.xyz`）按本仓库 `coulomb_energy` 复算得 40.596475（其坐标仅 8 位小数、行范数
   0.999–1.001，解释了 2.5e-5 的差异），其两两内积多重集与本仓库找到的构型完全一致。

**猜测最优构型**（数值刻画，17 位坐标由 `numerics/optimize.py` 写入 `numerics/reference_config.json`）：

- C2v 对称：存在一个二重旋转轴与两张过轴镜面，三者均把构型映到自身（11/11 点匹配，机器精度验证）；
- 轨道分解 11 = 1 + 2 + 2 + 2 + 4（1 个轴上点、3 对镜面内点对、1 个四点一般轨道）；
- 55 个点对共出现 **20 个**不同内积值，多重集见 `PROGRESS.md` 第 2 节——没有像 N = 7/8/9 那样
  的少量距离类型，这是 N = 11 没有简单闭式单参数族的数值根源；
- 结构来源：正二十面体收缩一条棱（两相邻顶点并为其归一化中点）后弛豫，恰好弛豫到该全局最小构型
  （本仓库数值验证：40.79434661663611 → 40.59645050819061）；「去掉一个顶点的二十面体」弛豫后是
  另一个局部极小 40.615117337，**不是**全局最优——文献综述中两者常被混为一谈；
- 最小点间距 0.977844807…。

## 3. 两阶段验收标准

**第一阶段（严格数值，本阶段已通过）**

1. `python3 thomson-n11/numerics/optimize.py` 退出码为 0：≥ 40 个随机起点的 scipy 多起点优化
   找到的最优能量必须满足 `|E_best − 40.596450508| < 1e-5`，并把最优坐标以 17 位有效数字写入
   `numerics/reference_config.json`（该文件是确定性再生成产物，已列入 `.gitignore`，
   两次运行字节一致，sha256 记录在 `PROGRESS.md`）；
2. `git -C thomson-n11 status --porcelain` 输出为空（工作树干净）；
3. `thomson-n11/formal/lean/ComparatorChallenges/*.lean` 存在。

**第二阶段（Lean，后续运行）**

1. 安装 Lean 工具链（`lean-toolchain` 钉 `leanprover/lean4:v4.34.1`，Mathlib 钉
   `d13f23b723b8a846827a245b89c10fc7d3f11612`，与参考仓库 N = 7 工程同款；**禁止 `lake update`**）；
2. `bash formal/lean/scripts/check.sh` 逐步通过：哈希（`scripts/pin_hashes.sh` 先钉
   `SHA256SUMS.txt`）、前言一致性、token 扫描、`lake build`（挑战文件恰有 2 个 `sorry` 警告）、
   公理检查（只允许 `propext, Classical.choice, Quot.sound`）、逐常量语句比对；
3. `bash formal/lean/scripts/negative-control.sh` 通过（语句比对确有牙齿：篡改 M1 不等号必须被抓）；
4. 里程碑 M0 → M1 → 最终定理依次完成，最终定理的形态按 `notes/strategy.md` 的隐式刻画路线补进
   挑战文件。

## 4. 当前状态

| 事项 | 状态 |
| --- | --- |
| 仓库骨架（README/PROGRESS/notes/formal/numerics/scripts） | ✅ 本次完成 |
| 数值复现 E₁(11) = 40.596450508（含勘误裁定） | ✅ 本次完成，验收门 1 通过 |
| Lean 挑战命题（基础定义 + M0/M1，全 `sorry`） | ✅ 本次完成（未编译，见下） |
| Lean 包构建 / `check.sh` / 负控制 | ⏸ 未运行：本机无 Lean 工具链（`elan toolchain list` 为空），留给后续运行 |
| M0 / M1 / 最终定理的证明 | ⏬ 未开始（见 `notes/strategy.md`） |

## 5. 仓库结构

    thomson-n11/
    ├── README.md            本文件
    ├── PROGRESS.md          工作日志：本次做了什么、验收结果、遗留问题（后续运行接着写）
    ├── formal/lean/         自包含 Lake 包（name = "ThomsonN11"，仅依赖 mathlib）
    │   ├── lakefile.toml / lake-manifest.json / lean-toolchain / .gitignore
    │   ├── ThomsonN11.lean              根模块（import ThomsonN11.Solution）
    │   ├── ThomsonN11/Solution.lean     证明占位（import Mathlib + 说明）
    │   ├── ComparatorChallenges/ThomsonN11.lean   固定挑战命题（2 个 sorry）
    │   └── scripts/         check.sh、pin_hashes.sh、DumpBody.lean、compare_statements.py、
    │                        CheckAxioms.lean、negative-control.sh（自参考仓库适配）
    ├── numerics/
    │   ├── energy.py        coulomb_energy(X)：n×3 坐标 → Σ_{i<j} 1/‖xi−xj‖
    │   ├── optimize.py      60 起点多起点优化 + 验收断言（退出码即验收门）
    │   └── reference_config.json   （再生成产物，gitignore）
    └── notes/strategy.md    攻坚路线与 N = 11 的特有机会/风险

参考材料（不在本仓库内，勿改动）：`../references/thomson-n7-lean/`（N = 7 已验证工程，验收脚本与
挑战文件写法的蓝本）、`../references/klt-n8-paper.pdf`（KLT N = 8 论文，方法参考）。
