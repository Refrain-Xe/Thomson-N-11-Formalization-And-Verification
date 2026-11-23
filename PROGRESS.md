# PROGRESS（工作日志）

本文件由各次运行依次追加。当前记录：**奠基运行，2026-10-02**（第 1–5 节）；
**升级运行 v2，2026-10-02**（第 6 节：负控制与验收门加固；6.4 首版有误，
**v2.1 复审修复**见 6.6，并附 Lean 侧实跑结果）；
**Phase 0–2 攻坚运行，2026-11-23**（第 7 节：80-dps $C_{2v}$ 驻点与黎曼谱诊断、精确有理 $S_3$/$(2,9)$ 三点 SDP 扫阶与本征间隙根因定位、Lean 4 内核形式化证毕 `M0`/`M1`/`thomson_eleven_sdp_M10`/`thomson_eleven_upper_bound`）。

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

### 6.4 没有跑过的检查（如实记录；**本节首版有误，见 6.6 勘误**）

- **Lean 构建在 v2 提交时未运行**。本节首版把理由写成「本机无 elan/lake/lean／无 Lean 工具链」——
  **这是错的**：我当时只跑了 `which elan lake lean`（三者在 PATH 外 → not found），就把
  「不在 PATH」误读成「机器没装」。实际 `~/.elan` 下有完整工具链（见 6.6 复核与勘误）。
  v2 提交时（21:01–21:05）未做任何 Lean 侧检查的**真实**原因是：我没有检查 `~/.elan`。
  正确记录应为「工具链在 `~/.elan/bin`，未加入当时 shell 的 PATH，我未发现」。
- v2 已做的替代验证：桩 `lake` 逐项实测判定逻辑（8 种篡改均 exit 1），**不验证 Lean 本身**；
  `bash -n` 校验加固后的 `check.sh`；`python3 -m py_compile` 校验改后的 `optimize.py`。

### 6.5 v2 验收门（工作流命令逐字执行）

| 门 | 命令 | 结果 |
| --- | --- | --- |
| 1 | `python3 thomson-n11/numerics/optimize.py` | ✅ 退出码 0（E_best = 40.596450508190578，\|gap\| = 1.906e-10；reference_config.json sha256 仍为 90ae9afd…，与 1.2 记录一致） |
| 2 | `python3 thomson-n11/numerics/optimize.py --selftest` | ✅ 退出码 0，打印 PASS（±0.5 两个错参考均被拒，正控制通过） |
| 3 | `git -C thomson-n11 status --porcelain` | ✅ 输出为空 |

### 6.6 复审修复（2026-10-02 晚，v2.1）：勘误 6.4 并实跑 Lean 侧检查

复审（medium）指出 6.4 的「本机无 elan/lake/lean」不属实。逐项复核确认（本次运行执行）：

    ls ~/.elan/bin                → elan lake lean leanc leanchecker …（工具链在，只是不在 PATH）
    ~/.elan/bin/lake --version    → Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)
    ~/.elan/toolchains/           → leanprover--lean4---v4.34.1（= lean-toolchain 钉的版本）
    git -C ../thomson-n9/formal/lean/.lake/packages/mathlib rev-parse HEAD
                                  → d13f23b723b8a846827a245b89c10fc7d3f11612
                                    （与 n11 lake-manifest.json 钉的 mathlib rev 逐位相同；
                                     9 个依赖包 rev 经比对全部一致；mathlib olean 8548 个）

即本机工具链 + 同 rev 预编译 Mathlib 均在（n9 于 19:19–19:24 构建过），v2 完全有条件跑 Lean 侧。
教训已记：**PATH 探测的负结果 ≠ 工具不存在；本版起 Lean 侧检查照跑，记录照实。**

#### 6.6.1 实跑结果（全部本次执行，命令与关键输出）

离线复用 n9 的包：把 `formal/lean/.lake/packages/` 下 9 个依赖目录软链到 n9 的同名目录
（`.lake/` 已被 `formal/lean/.gitignore` 忽略，不污染工作树；两仓库 manifest 的包 rev 逐位
一致，lake 直接接受，零下载）。

    export PATH="$HOME/.elan/bin:$PATH"
    lake exe cache get                     → No files to download / Already decompressed 8908 file(s)
    /usr/bin/time -p lake build ThomsonN11 ComparatorChallenges
                                           → Build completed successfully (8928 jobs)，20.77 s
                                             恰 2 条警告：ComparatorChallenges/ThomsonN11.lean:78:8
                                             与 84:8 "declaration uses `sorry`"；Solution 零警告
                                             （缓存重建 rc=0，lake 5 对缓存模块 "Replayed" 并重发警告）

**v1 第 2 节「挑战文件未经编译验证」的最大风险就此关闭**：挑战文件在钉死的工具链 + 钉死 rev 的
Mathlib 上完整 elaborate 通过，sorry 数恰为设计的 2（M0/M1）。同时关闭 v1 第 4 节遗留 1 的
manifest 疑问：原样拷贝（根包名仍是 ThomsonN7）不引发任何错误，无需改。

加固版 `bash scripts/check.sh` 全量实跑，退出码 1，逐 步状态：

| 步骤 | 结果 |
| --- | --- |
| 1 哈希 | 按设计跳过（SHA256SUMS.txt 未钉） |
| 2 前言 / 3 token / 3b 卫生 | 通过（Solution 占位：2 按设计 DEFERRED；3、3b 零命中） |
| 4 工具链 | 通过（cache get 零下载） |
| 5 构建+判定 | **通过**：源级 sorry 计数 2/0，日志级警告 2/0，构建 rc=0 |
| 6 公理 | **按设计失败**：CheckAxioms 引用 `ThomsonN11.thomson_eleven_M0/M1`，Solution 占位未声明 → unknown identifier → 加固判定 `AXIOM DUMP FAILED` + exit 1（判定逻辑实弹生效；证明写入 Solution 后此步才可能通过） |
| 7 语句比对 | 脚本未到达（6 已止步）；手动单跑：Challenge.tsv 10 常量 dump 成功；Solution 侧 0 行 → 比对按设计 FAILED（exit 1），全部 10 常量报 missing |

    bash scripts/negative-control.sh    → NEGATIVE CONTROL OK（退出码 0）
                                          篡改 M1 不等号后：mismatches 恰为
                                          ['ThomsonN11.thomson_eleven_M1'] 且 FAILED——语句比对确有牙齿

#### 6.6.2 仍未运行（如实记录）

- Lean Comparator / 第二内核（nanoda）：任务书未要求，未配置（v1 同）。
- check.sh 步骤 6/7 的**通过**：待 M0/M1 证明写入 Solution（奠基设计如此），当前失败均为设计内。

---

## 7. Phase 0–2 攻坚运行（2026-11-23）：80-dps 驻点诊断、三点 SDP 本征松弛间隙定位与 Lean 4 形式化证明

### 7.1 Phase 0A：80-dps $C_{2v}$ 边收缩二十面体驻点与 $22\times 22$ 黎曼 Hessian 谱

新增 `numerics/bounds/phase0_candidate.py` → `numerics/bounds/results/phase0_candidate.json`：

- 采用**北极有理球极投影** $(u,v) \mapsto \bigl(\frac{2u}{1+u^2+v^2}, \frac{2v}{1+u^2+v^2}, \frac{1-u^2-v^2}{1+u^2+v^2}\bigr)$（南极固定在 $(0,0,-1)$）无根号参数化 $C_{2v}$（$1+2+2+2+4$）5 维对称子流形 $(t_1, t_2, t_3, u_4, v_4)$；
- 在 80-dps `mpmath` 下牛顿迭代至切向梯度 $\|\nabla_{S^2} E(X^*_{11})\|_\infty = 8.52 \times 10^{-81}$，能量：
  $$E^*(11) = 40.5964505081906053866355313583344730183533640678192039000471\dots$$
- 次低局部极小（$C_{5v}$ 去顶二十面体 $1+5+5$）80-dps 能量为 $40.61511733694649722478\dots$（间隙 $+0.0186668288$）；
- 全球面 $22\times 22$ 黎曼 Hessian 谱：3 个 $\mathfrak{so}(3)$ 旋转零模（$\le 1.73\times 10^{-80}$）与 19 个严格正特征值，$\lambda_{\min}(H_0) = 0.0906732176562291324367\dots$，$\lambda_{\max}(H_0) = 7.6248624744517\dots$（5 维 $C_{2v}$ 子空间最小特征值 $0.8103354558\dots$）；
- 全部 55 对点对分裂为 **20 个不同内积轨道**，最小内积 $m^* = -0.999022793459447612728\dots$（重数 2，两对不相交近对跖点 `(3,6)` 与 `(4,5)`），次小内积 $-0.94331002254210\dots$（重数 2），最大内积 $+0.52190976643867\dots$（重数 2），最小能级间隔 $g_{\min} = 0.00369731146725\dots$（L06 与 L07 之间）。

### 7.2 Phase 0B：精确有理 $S_3$ / $(2,9)$ 三点 SDP 阶梯扫描与本征间隙根因定位（Path B 确立）

新增纯 `Fraction` 精确引擎 `numerics/bounds/{exact_linalg,sym_cap_sdpa,sym_strip_sdpa,phase0_sdp_sweep,phase0_gap_diagnosis,verify_all}.py`，配合 200/224-bit `SDPA-GMP` 产出 `certificates/` 下 **13 张精确有理证书**（共 296 个半正定块，全部经精确 `Fraction` $LDL^T$ 与三点组合恒等式 `identity_error = 0` 独立复验）：

1. **全局 $S_3$（$a_0 = -1$）阶梯**：
   - $(M,K) = (6,6)$：`40.5333157018172514`（$\Delta = 0.06313481$）
   - $(M,K) = (7,7)$：`40.5453147857027282`（$\Delta = 0.05113572$）
   - $(M,K) = (8,8)$：`40.5514942893318988`（$\Delta = 0.04495622$）
   - $(M,K) = (9,9)$：`40.5541606368310156`（$\Delta = 0.04228987$）
   - **$(M,K) = (10,10)$**：**`40.5554717043707456`**（$\Delta = 0.04097880$，$R_1 = 2.07\times 10^{-33}$，$R_2 = 5.92\times 10^{-31}$，已入 Lean 4 内核定理 `thomson_eleven_sdp_M10`）
   - **$(M,K) = (12,12)$**：**`40.5569603294090371`**（$\Delta = 0.03949018$，224-bit `SDPA-GMP` `9541.6s` `pdOPT`，$R_1 = 5.25\times 10^{-32}$，$R_2 = 2.31\times 10^{-29}$，26 块 `identity_err = 0`）。
   在 $(12,12)$ 处，$F_0\dots F_8$ 活跃（$\operatorname{tr} F_8 = 0.02057$），奇阶 $F_9 \approx 3.44\times 10^{-20}$、$F_{11} \approx 5.72\times 10^{-23}$ 严格失活，偶阶 $F_{10} = 1.05\times 10^{-4}$ 激活（与正二十面体群 $I_h$ 球谐不变量度数 $\ell \in \{0, 6, 10, \dots\}$ 完全吻合），两阶跃升合计仅增 `+0.0014886`，实证确认三点 SDP 渐近饱和于 $\approx 40.557 < E^*(11)$。
2. **截断与 $(2,9)$ typed 条带加强探针**：
   - 下界截断 $a_0 = -1023/1024 < m^*$：$(6,6)\to 40.53332037$，$(8,8)\to 40.55151609$，$(10,10)\to 40.555539579695$（$\Delta = 0.04091093$），**$(12,12)\to 40.5569708647357743$**（`9608.9s` `pdOPT`，$R_1 = 4.76\times 10^{-32}$，$R_2 = 5.57\times 10^{-29}$，$\Delta = 0.03947964$）；
   - 上界截断 $a_0 = -1, b_0 = 53/100$：$(8,8)\to 40.55178721$；
   - 深帽截断：$(8,8), a_0 = -49/50 \to 40.55495240$；$a_0 = -9/10 \to 40.58493495$（真球面约束极小为 `40.63245`，三点 SDP 仍有 `0.0475` 松弛间隙且未越过 $E^*(11)$）；
   - $(2,9)$ typed 极环条带：`[-1, -1023/1024]` 在 $(6,6)$ 下为 `40.53687092`；含 $m^*$ 的极窄条带 `[-9991/10000, -999/1000]` 在 $(7,7)$ 下为 `40.54800350`（$\Delta = 0.048447$）。
3. **本征松弛间隙（$\Delta \approx 0.0395$）的几何根因（`results/phase0_gap_diagnosis.json`）**：
   - 在 $X^*_{11}$ 真矩上的 1D 多项式次估 LP 在 $M=8$（$D=14$）时已达 `40.59645010`（间隙 $4.04\times 10^{-7}$），排除多项式逼近阶数瓶颈；
   - $(10,10)$ 对偶最优伪矩的 9 节点 Gauss–Christoffel 测度在 $t_1 = -0.999637$ 处放置了 **`3.3946` 对分数对跖点**（$H^*(-1) = \varphi(-1) = 0.5$），在 $t \approx \mp 1/\sqrt{5}$ 附近放置 `18.01` 与 `21.87` 对二十面体邻接点对；
   - 真实 $\mathbb{R}^3$ 球面含 $k$ 对精确对跖点的最小能量为：$k=0: 40.596451$，$k=1: 40.596907$（仅 $+4.57\times 10^{-4}$），$k=2: 40.597677$（仅 $+1.23\times 10^{-3}$），$k=3: 40.625784$（$+0.0293$），$k=4: 40.780435$（$+0.1840$）。$k=1,2$ 真构型阻断了近对跖区间排除，而三点 SDP 缺少四点秩 3 条件 $\det G_4 = 0$，利用约 $3.4$ 对分数对跖点吸收 11 点相对 12 点二十面体的拓扑缺陷而免付三维嵌入受挫代价。

### 7.3 Phase 1 & Phase 2（Path B）：Lean 4 内核形式化证明与全门验收

在绝对不修改 `ComparatorChallenges/ThomsonN11.lean`、零 `sorry`、零 `native_decide`、仅使用 `[propext, Classical.choice, Quot.sound]` 三条标准公理的前提下，完成 `ThomsonN11/StageB/` 与 `ThomsonN11/Solution.lean` 形式化：

1. **里程碑 `thomson_eleven_M0`（`55/2 = 27.5`）与 `thomson_eleven_M1`（`155/4 = 38.75`）**：在 `Solution.lean` 中由直径不等式及二次次估 $f(t)=\frac{7}{10}+\frac{2}{5}t+\frac{7}{40}t^2$（六平方 Lukács 证书 + 一/二阶球谐矩，给出 `583/15 > 155/4`）直接证毕。
2. **加强全局三点 SDP 下界 `thomson_eleven_sdp_M10`（`2027773585218537 / 50000000000000 = 40.55547170437074`）**：
   - `StageB/ThreePoint.lean`：球面三点 Bachoc–Vallentin 正定性（复 de Moivre 展开）与 11 点 $S_3$ / $(2,9)$ 组合装配恒等式；
   - `StageB/PolyKronDefs.lean` + `PolyKron.lean` + `PolyKronFast.lean`：**零 Mathlib（纯 `Init`）数据层架构**，使 `SdpCertHarmData`、`SdpCertSosData` 与全部 19 个并行切片模块 `SdpCertSosSlice{M9..9}` 免除 Mathlib 导入（单进程内存 `< 300 MB`），由 `export_lean_sdp.py`（`B = 72`）导出纯整数 Cholesky 与 2D-Kronecker 证书，在 `StageB/SdpCert.lean` 中收口 `global_sdp_lower_bound`。
3. **精确有理 $C_{2v}$ 构型上界 `thomson_eleven_upper_bound`（`2029822525409531 / 50000000000000 = 40.59645050819062`）与双边夹逼 `thomson_eleven_bounds_sandwich`**：
   - 由 `export_lean_upper.py` 导出 100% 纯 `ℤ` 齐次球极投影见证 `StageB/UpperBound.lean`（距 $E^*(11)$ 仅 $1.46\times 10^{-14}$），规避 `ℚ` 通分开销。
4. **验收门加固与实跑**：
   - `python3 numerics/optimize.py` & `optimize.py --selftest`：exit 0；
   - `python3 numerics/bounds/sym_cap_sdpa.py --selftest` & `sym_strip_sdpa.py --selftest`：exit 0；
   - `python3 numerics/bounds/verify_all.py`：1322.84s exit 0（13 张证书 296 个 PSD 块 + 21 组有理球面构型 + NC1–NC4 四项负对照全过）；
   - `bash formal/lean/scripts/check.sh`（全包 `SHA256SUMS.txt` 哈希锁定、基础定义逐字核对、去注释禁用记号扫描、`lake build` 源级/日志级 `sorry` 2/0、5 项顶层定理 `#print axioms` 严格三公理白名单、10/10 挑战常量比对 OK）与 `bash formal/lean/scripts/negative-control.sh`（语句翻转 NC1 + 内核篡改 NC2 双拦截）：全部 exit 0。

---

## 8. 独立审校加固与四点 SDP 层级实测运行（2026-11-24）

### 8.1 修复前序尝试的复现缺陷、缺失产物与门控盲区
1. **修复 `phase0_gap_diagnosis.py` 崩溃并补全全部诊断计算**：移除对已清理临时文件 `results/sdpa_work/n11_am1_M10_K10/*.result` 的硬编码依赖及残留 `eval()`，改为从已提交精确证书直接读取 `(10,10)` 与 `(12,12)` 谐波块矩阵并在独立 `TemporaryDirectory` 中求解对偶矩，同时新增可复现的 $X^*_{11}$ 真矩 1D 次估 LP（$M=4,6,8,10,12$）与 $k$-对跖（$k=0\dots 5$）球面约束极小能量阶梯计算，独立生成 `results/phase0_gap_diagnosis.json`。
2. **补全 `(2,9)` typed 条带精确证书、证书汇总账本与高速精确校验**：
   - 在 `exact_linalg.py:is_positive_definite` 中采用精确整数 Bareiss Sylvester 顺序主子式消元替代高维有理分式 GCD 爆炸的逐列分式 $LDL^T$，并在 `sym_cap_sdpa.py` 中预收缩三点恒等式张量幂，在保持 100% 纯整数/有理数零浮点妥协的前提下将全量证书复验耗时从 `1322.8s` 压缩至数分钟以内；
   - 为 `sym_strip_sdpa.py` 补全 `write_certificate` 与 `verify_certificate_file`（含精确 Bareiss 正定检验、Lukács 残差重算及 `(2, n-2)` 组合恒等式零误差校验），生成并入库 2 张 `(2,9)` 条带精确证书（`n11-symstrip-n11_strip_m1_m1023o1024_M6_K6.json` 与 `n11-symstrip-n11_strip_m9991o10000_m999o1000_M7_K7.json`）；
   - 更新 `phase0_sdp_sweep.py` 生成此前缺失的 `results/phase0_sdp_sweep.json`（覆盖全部 **15 张精确证书、410 个半正定块**），并将 `verify_all.py` 扩展至 `symcap + symstrip` 双族全量复验与 **6 项负对照（NC1–NC6）**。
3. **加固 Lean 4 门控脚本 `check.sh`、`negative-control.sh` 与文档注释**：
   - 修正 `ThomsonN11/StageB/ThreePoint.lean` 中 `cap_assembly_11` 文档注释遗留的 $N=9$ 常数（统一为定理陈述中的 `e/55`、`9*sym3`、`s 1 1 1 / 10`）；
   - 修复 `formal/lean/scripts/check.sh` 第 1 步仅扫 `git ls-files` 漏检未跟踪包内文件的漏洞（同步扫描工作树包目录全集），并修复第 3 步 `strip_lean_comments` 未识别字符串/字符字面量（如 `"/-"` 伪造块注释包裹 `skipKernelTC`）的解析漏洞，在 `negative-control.sh` 中新增 **NC3 字符串伪注释偷渡拦截测试**，重新运行 `pin_hashes.sh`、`check.sh` 与 `negative-control.sh` 全部 exit 0。

### 8.2 Phase 0C：$S_{11}\times O(3)$ 约化耦合四点 SDP 层级实测（`phase0_4pt_probe.py`）
新增 `numerics/bounds/phase0_4pt_probe.py` $\to$ `numerics/bounds/results/phase0_4pt_probe.json`，实现完整的四点局部与全局半定约束（$\det G_4 = 0$ 理想乘子、$\mathbb{Z}_2\times\mathbb{Z}_2$ 4 点 SOS、Binet–Cauchy `Harm4_odd`、对旗 `Flag2_even` 及 $(\mathbb{R}^3)^{\otimes d}$ 全局点对张量块 `GlobNat_d*`/`GlobAx_d*`，全部通过随机球面构型精确 `Fraction` 恒等式零误差自测）：
- $M=4$（$D_3 = 6$）：纯三点 `40.328025578797` $\to$ 耦合 $D_4 = 6$ 四点 **`40.491098499829`**（增益 **`+0.163072921032`**）；
- $M=5$（$D_3 = 8$）：纯三点 `40.506357627168` $\to$ 耦合 $D_4 = 6$ 得 `40.506512909564`（`+0.00015528`），耦合 $D_4 = 8$ 得 **`40.514179689124`**（增益 **`+0.007822061955`**）；
- $M=8$（$D_3 = 14$）：纯三点 `40.551494289332` $\to$ 耦合 $D_4 = 4, 6$ 增益为 `0.000000000000`（`< 2e-13`），实证确立低阶四点（$D_4 \le 8$，天花板 `40.51418`）尚不足以分辨 9 个分数二十面体伪原子，要跨越 `~40.557` 三点松弛极限需推进至 $D_4 \ge 14\text{--}18$ 高阶四点 SDP 或多极联合分支定界。
