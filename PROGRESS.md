# PROGRESS（工作日志）

本文件由各次运行依次追加。当前记录：**奠基运行，2026-10-02**（第 1–5 节）；
**升级运行 v2，2026-10-02**（第 6 节：负控制与验收门加固）。

## 1. 本次做了什么

### 1.1 仓库骨架

- 建立本仓库目录结构（见 `README.md` 第 5 节）。
- `formal/lean/`：`lake-manifest.json`、`lean-toolchain`、`.gitignore` 从
  `references/thomson-n7-lean/formal/lean/` **原样拷贝**（未运行 `lake update`）；
  `lakefile.toml` 按任务书改包名 `ThomsonN11`，Mathlib 钉同一 rev `d13f23b723b8a846827a245b89c10fc7d3f11612`。
  ⚠️ 注意：原样拷贝来的 `lake-manifest.json` 末尾 `"name": "ThomsonN7"` 是参考仓库的根包名，
  与本包名不一致；是否需要连同改成 `ThomsonN11` 待首次 `lake build` 时验证（见第 4 节遗留问题）。
- `formal/lean/ComparatorChallenges/ThomsonN11.lean`：基础定义 `R3`/`SphereConfig`/
  `coulombEnergy`/`cyl` 及两条辅助引理 `norm_sq_cyl_sub`/`norm_sq_cyl` 从参考仓库挑战文件
  **逐字搬运**（用脚本逐块核对与原文一致），仅命名空间与文件头不同；里程碑命题
  `thomson_eleven_M0`（E ≥ 55/2）与 `thomson_eleven_M1`（E ≥ 155/4）以 `sorry` 结尾。
  N = 11 无简单单参数闭式族，故挑战文件**不放**候选构型定义；最终命题的隐式刻画形态写在
  `notes/strategy.md`，不进 Lean（任务书明确要求）。
- `formal/lean/ThomsonN11.lean`（根模块，`import ThomsonN11.Solution`）与
  `formal/lean/ThomsonN11/Solution.lean`（占位：`import Mathlib` + 未来证明结构说明）。
- `formal/lean/scripts/`：`check.sh`（哈希步在 `SHA256SUMS.txt` 未钉时允许跳过；前言一致性检查
  在 Solution 为占位时挂起；claims.tsv 索引步删除——还没有论文）、`DumpBody.lean`（原样）、
  `compare_statements.py`（SKIP 集合清空：M0/M1 都是要被证的）、`CheckAxioms.lean`、
  `negative-control.sh`（篡改 M1 不等号须被抓）、`pin_hashes.sh`（参考仓库没有此脚本，
  按其 `SHA256SUMS.txt` 的格式新写，用于把包文件哈希钉进 `SHA256SUMS.txt`）。

### 1.2 数值复现与勘误（本次最重要的发现）

任务书要求 `optimize.py` 断言 `|E_best − 39.783856229| < 1e-5`。实施过程中发现**该参考值
错误**，完整证据链与升级裁定记录在第 3 节。结论：`E₁(11) = 40.596450508…`，
`optimize.py` 与 `README.md` 改钉 `REF_ENERGY = 40.596450508`（容差 1e-5 不变）。

`numerics/energy.py`：`coulomb_energy(X)`，n×3 坐标 → Σ_{i<j} 1/‖xi−xj‖。
验证（命令与输出，本机 python3 3.13.13 / numpy 2.4.6 / scipy 1.17.1）：

    五角双锥 (N=7)   → 14.452977414221344   （文献/参考仓库：14.452977414…）
    方反棱柱 (N=8)   → 19.67528786123276    （KLT 论文：19.6752878612）
    二十面体 (N=12)  → 49.16525305762881    （Wikipedia：49.165253058）

`numerics/optimize.py`：60 个固定种子随机起点，每起点 L-BFGS-B（球面径向投影参数化 + 解析梯度，
梯度对有限差分校验通过，相对误差 1.9e-9）+ SLSQP 约束抛光；最优者再经 12 轮穷尽 L-BFGS 抛光。

    $ python3 thomson-n11/numerics/optimize.py ; echo EXIT=$?
    N = 11 points on S^2, 60 seeded random starts (seed = 20261002)
      after  60 starts: best E = 40.596450508191, this start E = 40.596450508
    distinct local minima within 1e-7: 1
        E = 40.596450508191   reached by 60 start(s)
    global best: E = 40.596450508190578
    stationarity: max|tangential gradient| = 2.10e-10, max|row norm - 1| = 1.11e-16
    |E_best - 40.596450508| = 1.906e-10 (tolerance 1e-05)
    wrote .../numerics/reference_config.json
    OK: reproduced the reference energy to within 1e-05
    EXIT=0

确定性：连续两次运行输出的 `reference_config.json` 字节一致，
sha256 = 90ae9afd2acf6893613309e737a266e28031e669dc769baf8125e475a838be53。
该文件是再生成产物，已列入仓库根 `.gitignore`（保证验收门 2「工作树干净」对不同环境稳健）。

### 1.3 最优构型结构（全部为本次数值验证，非文献转录）

- **对称性 C2v**：协方差阵 `XᵀX` 最小特征值（3.554503）对应的主轴是一个二重旋转轴
  （x ↦ 2(a·x)a − x 把构型映到自身，11/11 点在 1e-6 内匹配）；含该轴的两张镜面同样 11/11 匹配。
- **轨道分解** 11 = 1 + 2 + 2 + 2 + 4。
- **55 个点对、20 个不同内积值**，多重集（数值，聚类容差 1e-6）：

      -0.999022793×2  -0.943310023×2  -0.805954897×2  -0.642378985×4  -0.552681463×2
      -0.500513593×4  -0.468917100×1  -0.465219789×2  -0.415314314×4  -0.389086401×1
      -0.332252270×4  +0.168359699×4  +0.299126591×1  +0.314415020×4  +0.370998333×4
      +0.429421384×2  +0.445436331×4  +0.505766180×4  +0.515307141×2  +0.521909766×2

- **结构来源**：二十面体收缩一条棱（相邻两顶点并为归一化中点）未弛豫能量 40.79434661663611，
  弛豫后精确到 40.59645050819061 = 全局最小。「去掉一个顶点的二十面体」（C5v 的 5+5+1 环族，
  双参数扫描 + Nelder-Mead，300 起点）最优仅 40.615117337——是另一个局部极小，不是全局；
  5+6 双环族最优 41.044302330。
- 最小点间距 0.977844807…。

## 2. 验收结果（工作流三验收门，按原命令逐字执行）

| 门 | 命令 | 结果 |
| --- | --- | --- |
| 1 | `python3 thomson-n11/numerics/optimize.py` | ✅ 退出码 0（输出见 1.2；|gap| = 1.9e-10 < 1e-5） |
| 2 | `git -C thomson-n11 status --porcelain` | ✅ 输出为空（提交后验证，见 1.2 关于 reference_config.json 的处理） |
| 3 | `thomson-n11/formal/lean/ComparatorChallenges/*.lean` 存在 | ✅ `ComparatorChallenges/ThomsonN11.lean` 存在 |

**没有跑过的检查（如实记录）**：

- `lake build` / `formal/lean/scripts/check.sh` 的构建部分 / `CheckAxioms.lean` /
  `negative-control.sh`：**未运行**。本机装了 elan（`~/.elan/bin`）但没有任何工具链
  （`elan toolchain list` → "no installed toolchains"），且 Mathlib 缓存不可得，本次未安装下载。
  因此 `ComparatorChallenges/ThomsonN11.lean` **未经编译验证**；其风险由「全部可执行内容逐字
  取自参考仓库中已编译通过的文件（逐块脚本核对）+ 里程碑命题语句与参考文件中同形命题结构一致」
  缓解，但不能视为已验证。
- 已跑过的无构建检查（记录）：
  - `SKIP_BUILD=1 bash scripts/check.sh`（在 `formal/lean/` 下）→ 步骤 1 按设计跳过
    （未钉哈希）、步骤 2 按设计挂起（Solution 为占位）、步骤 3 token 扫描无输出，退出码 0；
  - `bash scripts/pin_hashes.sh` 写出 `SHA256SUMS.txt`（格式与参考仓库一致，且其中
    `.gitignore` 一行哈希 `ccaa0df3…` 与参考仓库的 `.gitignore` 哈希相同——原样拷贝的旁证），
    `--check` 全部 ok；随后按设计删除该文件（哈希留待挑战语句定稿后再钉）；
  - `bash -n` 校验三个 shell 脚本、`python3 -m py_compile` 校验两个 numerics 脚本与
    `compare_statements.py`，均通过。
- Lean Comparator / 第二内核（nanoda）：参考仓库有，本仓库按任务书未要求，未配置。

## 3. 勘误：任务书参考能量 39.783856229 → 40.596450508

发现过程：`optimize.py` 初版按任务书钉 39.783856229 时，60 个随机起点全部收敛到
E = 40.596450508191，无一达到断言值。排查步骤（全部有运行记录）：

1. **能量函数正确性**：N=7 → 14.452977414221344、N=8 → 19.67528786123276、
   N=12 → 49.16525305762881，与文献一致（见 1.2）。
2. **优化器正确性**：同一多起点方法复现 N=7 → 14.452977414、N=9 → 25.759986531、
   N=10 → 32.716949460、N=12 → 49.165253058（与文献差 ≤ 1.3e-10）。
3. **穷尽搜索 N=11**：L-BFGS-B（投影参数化）与 SLSQP（原生约束）两个独立优化器、60 随机起点、
   从 N=9/N=10 最优构型生长的 100 次插入、basin-hopping 300 步、结构族扫描（C5v 5+5+1 环、
   5+6 双环、二十面体去顶/缩棱）——最低能量始终是 40.596450508…，其切向梯度可压到 1e-10，
   沿随机切向微扰能量双向上升（真局部极小）。
4. **文献三角验证**（本次在线抓取）：
   - Wikipedia《Thomson problem》表：N=11 → 40.596450510，C2v，"edge-contracted icosahedron"
     （其 N=7/8/9/10/12 各行与本机计算一致）；
   - Wales–Ulker Cambridge Cluster Database（`table.html`）：N=11 → 40.5964505；
     其 `xyz/11.xyz` 坐标按本仓库 `coulomb_energy` 复算 = 40.596475（文件仅 8 位小数、
     行范数 0.999–1.001，解释 2.5e-5 差距），且与本次找到的构型内积多重集一致；
   - UBC 讲义 PDF 列 11 charges → 40.596450。
   - 数值 39.783856229 在任何 Thomson 表中都检索不到原文命中。
5. **升级裁定**：已通过升级渠道请示运行所有者，裁定采用方案 A：`optimize.py` 与 `README.md`
   改钉 `REF_ENERGY = 40.596450508`（容差 1e-5），写勘误说明（本节），Lean 挑战命题不动
   （M0 = 27.5、M1 = 38.75 均低于真实最小值 40.5964505，作为下界里程碑依然成立）。

## 4. 遗留问题（后续运行接着做）

1. **Lean 侧全部未验证**：安装 `leanprover/lean4:v4.34.1` 工具链 + Mathlib 缓存后，跑
   `SKIP_BUILD=1 bash formal/lean/scripts/check.sh` 先做无构建检查，再
   `bash formal/lean/scripts/check.sh` 全量（预期：挑战文件恰 2 个 `sorry` 警告；
   Solution 占位无警告；随后再证 M0/M1）。首次构建时同时验证 1.1 末尾提到的
   `lake-manifest.json` 根包名问题（如 Lake 报 name mismatch，把其 `"name"` 字段改为
   `"ThomsonN11"` 即可——这只影响根包名，不动任何依赖 rev）。
2. `scripts/pin_hashes.sh` 尚未运行，`SHA256SUMS.txt` 未钉（check.sh 当前按设计跳过哈希步）。
   挑战文件语句定稿后应钉一次。
3. 最终定理的 Lean 形态（隐式刻画 + 唯一性）未定稿：见 `notes/strategy.md` 第 5 节的
   两个候选写法，待 SDP 上界路线走通后定。
4. `optimize.py` 的起点数（60）对 N=11 的复杂地形是够的（60/60 同收敛），但若未来改种子，
   注意 N=11 的地形陷阱：文献值一度被任务书录错，且「去顶二十面体」是诱饵局部极小
   （40.615117337，仅比全局高 0.019）。
5. 数值侧下一步（若走严格区间路线）：用区间算术把最优构型的能量/梯度包住，
   产出机器可查证书（KLT 式），支撑 SDP 分裂的参数选择。

## 5. 复审修复记录（2026-10-02，奠基提交 7fb0f8f 之后）

复审发现一处 medium：挑战文件 `formal/lean/ComparatorChallenges/ThomsonN11.lean` 的注释仍
断言被勘误掉的错误参考能量（原第 9 行「minimum is E₁(11) ≈ 39.783856229」、原第 69-71 行
「M1 is within 1.034 of the conjectured optimum ≈ 39.783856229」），与 README/PROGRESS 的
勘误叙述互相矛盾。修复：

- 文件头改为「minimum is `E₁(11) ≈ 40.596450508`（erratum: 任务书原数字 39.783856229
  是错的——低于真实最小值，见 README 第 2 节与 PROGRESS 第 3 节）」——保留错误数字仅作
  显式标注的历史记录，杜绝误读；最小化构型描述同步补为 C2v「边收缩二十面体」；
- 里程碑段改为「M1 is within `1.85` of the numerically known optimum `≈ 40.596450508`」
  （真实差 40.596450508 − 38.75 = 1.846450508…，原「1.034」基于错误参考值），最终定理
  目标同步改为 `E₁(11) = 40.596450508…`；
- 命题本身（M0 = 55/2、M1 = 155/4）不变（复审确认其不受影响仍有效）。

修复后核对（本次运行执行）：逐块脚本核对 6 个搬运定义/引理与 M0/M1 命题语句逐字未动；
除上述显式标注的历史记录外，挑战文件不再出现 39.783…；全仓其余 39.783856229 出现处均为
README/PROGRESS/optimize.py 的勘误记录。复审方独立数值复算（另一 SLSQP 实现、种子 777、
60 随机 + 7 结构化起点）同样得全局 40.596450508191、次低极小 40.615117336946，与第 3 节
证据一致。三个验收门在修复后重跑通过（见第 2 节表格，命令不变）。

## 6. 升级运行（2026-10-02，v2：负控制与验收门加固）

本节由 v2 升级运行追加。动机直接来自 v1 的两条教训：**(a)** 任务书参考能量曾经录错
（39.783856229，第 3 节），当时的验收断言只靠「跑出来看输出」发现不一致——一个**没有牙齿的
验收门**（比较逻辑写错、永远放行）会把错误参考值也放过去；**(b)** v1 的 `check.sh` 若干检查
只打印不判定（token 扫描、sorry 计数），与 N = 7 蓝本一样「打印即通过」。本次升级把两处
都装上负控制。

### 6.1 参考能量改为读唯一可信来源（commit `622c096`）

`numerics/optimize.py` 不再硬编码 `REF_ENERGY`，改为 `load_reference_energy()` 读
`../thomson-workflow/data/energies.json` 的 `energies["11"].value`（三源校验数据文件：
Wikipedia / Wales–Ulker CCD / Deeter + 独立本机复算，见其 meta 块）。原常量保留为
`REF_ENERGY_FALLBACK = 40.596450508`（同一数字、同一来源），仅在数据文件不可达（如本仓库被
单独 clone）时使用，且**两种情况都打印 notice**（使用回退常量、或文件值与回退常量分歧
> 1e-9），静默分歧不可能。本次读取值与 v1 常量逐位一致（40.596450508），无冲突。

### 6.2 `--selftest` 负控制（commit `f9e28b1`）

断言逻辑抽出为 `acceptance(E, ref, tol)`（真实模式与自测共用同一条路径）；`--selftest`
用**故意错的参考能量（真值 ± 0.5）**各走一遍该路径，要求两者都必须触发拒绝（exit 1，打印
FAILED），再加正控制（真参考必须放行）。全部符合才打印 `PASS` 并以退出码 0 结束；任一不符
打印 `SELFTEST FAILED` 退出 1。喂给门的能量是真值优先：从上次真实运行产物
`reference_config.json` 重算坐标能量并与存储值核对（差 +1.4e-14）后才使用；文件缺失时回退用
参考值本身（输出中注明）。不重跑优化——受试的是门逻辑，不是优化器。真实模式除共用
`acceptance()` 外行为不变（实测退出码 0、产物字节不变）。

### 6.3 `check.sh` 加固（commit `c34a812`）

- 前言一致性：显式 `PREAMBLE MISMATCH` + exit 1（原先靠 `set -e` 静默退出）；
- token 扫描：解法文件出现任何违禁 token 即 FATAL（原先只打印，从不判定；扫描正则未动）；
- 新增步骤 3b 仓库卫生：git 跟踪了 `__pycache__`/`*.pyc` 即 FATAL。核实：本仓库 `.gitignore`
  自奠基起已含 `__pycache__/`（`git check-ignore -v` 确认生效），且 `git ls-files` 无任何
  字节码被跟踪，故升级要求的 `git rm -r --cached` 清理为**无操作**（nothing to clean），
  3b 使其保持如此；
- 构建步：去掉 `TIME_PRE` bash 数组前缀（macOS 自带 bash 3.2 下空数组展开 + `set -u` 是潜在
  「unbound variable」炸弹）；显式检查构建退出码；sorry 计数加判定——**源级计数为约束**
  （挑战文件独立 `sorry` 行恰 2、解法 0，与缓存重建无关），构建日志级计数兼容「缓存构建不重发
  警告」的情形（挑战文件警告出现时必须恰 2，解法警告必须 0）；
- 步骤 6–7：失败时点名日志文件再退出。

**失败路径逐项实测**（临时副本中每次只篡改一个因子，全部 exit 1 且打出对应判定行）：解法含
`sorry` → FORBIDDEN TOKEN；钉错哈希 → HASH MISMATCH；前言改一词 → PREAMBLE MISMATCH；
临时 git 仓库跟踪 pycache → TRACKED BYTECODE；桩 `lake` 退出 1 → LAKE BUILD FAILED；挑战
警告数 1 / 解法警告数 1 → SORRY-WARNING CHECK FAILED；挑战源码 3 个 `sorry` 行 →
SORRY-COUNT CHECK FAILED；新鲜构建（2 警告）与全缓存构建（0 警告）均通过步骤 5。正控制
（未篡改的真实树，`SKIP_BUILD=1 bash scripts/check.sh`）退出码 0。

### 6.4 没有跑过的检查（如实记录）

- **Lean 构建仍未运行**：本机无 elan/lake/lean（`which elan lake lean` 均无；v1 记录的工具链
  缺失依旧），`check.sh` 步骤 4–7 的 Lean 侧（真实 `lake build`、公理检查、语句比对、
  `negative-control.sh`）未执行；6.3 的桩测试只验证**判定逻辑**，不验证 Lean 本身。与 v1
  第 2/4 节一致，留给装好工具链的后续运行。
- `bash -n` 校验加固后的 `check.sh` 通过；`python3 -m py_compile` 校验改后的
  `optimize.py` 通过。

### 6.5 v2 验收门（工作流命令逐字执行）

| 门 | 命令 | 结果 |
| --- | --- | --- |
| 1 | `python3 thomson-n11/numerics/optimize.py` | ✅ 退出码 0（E_best = 40.596450508190578，\|gap\| = 1.906e-10；reference_config.json sha256 仍为 90ae9afd…，与 1.2 记录一致） |
| 2 | `python3 thomson-n11/numerics/optimize.py --selftest` | ✅ 退出码 0，打印 PASS（±0.5 两个错参考均被拒，正控制通过） |
| 3 | `git -C thomson-n11 status --porcelain` | ✅ 输出为空 |
