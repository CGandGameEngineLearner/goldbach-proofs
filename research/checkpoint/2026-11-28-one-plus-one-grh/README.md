# 全范围显式 1+1 例外集、短区间与 Linnik 二幂偏移表示（K = 22）· 上游固定快照与独立复核指南

**提交者**　千早爱音（[Visio-Vanitas](https://github.com/Visio-Vanitas)）。[中间命题提交稿](proof.md)

本目录提交强哥德巴赫（`1+1`）方向在 GRH + 已知经验界 $E(4\cdot 10^{18}) = 0$ 下的三项全范围显式中间定理及其 Lean 4（`v4.36.0`）形式化归约与零浮点计算证书，供仓库维护者与同行独立复核。所有数值证书、Lean 编译结果及外部解析接口均以独立重放审定为准。

---

## 1. 上游仓库与固定版本信息

- **上游仓库**：[`https://github.com/Visio-Vanitas/buchstab-switching`](https://github.com/Visio-Vanitas/buchstab-switching)（分支 `feat/one-plus-one-v436`，子目录 `1+1/`）
- **固定提交 SHA**：`f878d4a20513f020e5c4e857fd5d0aae2e644bdb`
- **Lean 工具链与依赖锁**（与本仓库 `lean/lean-toolchain`、`lean/lake-manifest.json` 及 CI `leanOptions` 完全一致）：
  - [`1+1/lean-toolchain`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1/lean-toolchain)：`leanprover/lean4:v4.36.0`
  - [`1+1/lake-manifest.json`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1/lake-manifest.json)：Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
  - [`1+1/lakefile.toml`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1/lakefile.toml)：`autoImplicit = false`、`relaxedAutoImplicit = false`、`maxSynthPendingDepth = 3`、`pp.unicode.fun = true`、`maxHeartbeats = 4000000`
- **GRH 声明对齐目标**：[`1+1/OnePlusOne/Core/Defs.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1/OnePlusOne/Core/Defs.lean) 中的 `DirichletLNonvanishingRightOfHalf` 与本仓库 `lean/PEqualNP/GRH.lean` 及 [`lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean) 逐字一致；**零 `native_decide`**（全部 30 个导出声明仅依赖 `[propext, Classical.choice, Quot.sound]` 及其子集）。

### 关键存档文件 SHA-256（以 `git clone -c core.autocrlf=false` 检出为准）

| 相对路径 | SHA-256 | 说明 |
|---|---|---|
| `1+1/scripts/certify_exceptional_short.py` | `78ac92bbfb0436a6dbba4eeb7d10fd141e89077a180b27abcbc4741a415345be` | 定理 1A / 1B 零浮点 80 位 `Decimal` 认证器 |
| `1+1/data/certify_exceptional_short_output.txt` | `3f3d5e76a774019c9919c76c2f65bd273b0b7705e001848a5ba2736bca418ac0` | 定理 1A / 1B 完整认证日志（15 个细胞 + 尾段） |
| `1+1/scripts/certify_linnik_r.py` | `1e3f3361ab63d2e7344d304a7347854fd0a4175096bc3d2dffeb1628f9e52481` | 定理 3（$K = 22$）零浮点圈法 + Bessel 转移矩阵认证器 |
| `1+1/data/certify_linnik_r_output.txt` | `9d95629ce2fc28b0b2c425dad4ade47abaf5d5db4c979bfbcb59954c2d0c6dc8` | 定理 3 认证日志（$r=22$ 跨越点、`L=79..139`、`L>=140`） |
| `1+1/scripts/quick_verify.py` | `afdfe9d432a6b1ed8219e90aa59f21697157b20af279900c6cec8619fad2a5c5` | AST 零浮点扫描 + 全量证书重放 + `Data.lean` + 静态审计 |
| `1+1/OnePlusOne/Certificates/Data.lean` | `ec254666c6fc9ec42c2256c518c8faaa18bd9ed195407ecdb958acbd10f37d54` | 纯内核 `by decide` / `norm_num` 整数证书表 |
| `1+1/OnePlusOne/Linnik/Reduction.lean` | `f6d506b69a6d763063b6858bacd6090cba8ce010695aa300313f6981665b6128` | 纯 Lean 无条件二进制哥德巴赫桥梁（$48 \le N \le 1.934\cdot 10^{25}$） |
| `1+1/OnePlusOne/Main.lean` | `9c488970ace0f49f70b97d234c7a66561d53f93dcd418e958f6d33bafc399e8d` | 顶层导出定理 `theorem_1A`、`theorem_1B`、`theorem_3A`、`theorem_3` |
| `1+1/AxiomsCheckOnePlusOne.lean` | `16dcaff63c8e462fa695b4a7190c6eec9b35e0f1cc5fb7875beb280f4da14211` | 30 条导出定理的 `#print axioms` 公理审计文件 |
| `1+1/comparator_output.txt` | `c66db4cd44135d748dba4881880d9fff440672c6c28a99f3fc0aadcb67df5867` | 三内核 `comparator` 实测复核完整日志 |

---

## 2. 供维护者独立执行的复核命令（POSIX shell）

```sh
git clone -c core.autocrlf=false https://github.com/Visio-Vanitas/buchstab-switching.git
cd buchstab-switching
git fetch origin f878d4a20513f020e5c4e857fd5d0aae2e644bdb
git checkout --detach FETCH_HEAD

# 1. Python 零浮点 AST 审计、证书全量重算对照与 Lean 静态洁净度扫描
cd 1+1
python3 -m py_compile scripts/*.py
bash -n comparator/run_comparator.sh
python3 -I scripts/quick_verify.py

# 2. Lean 4.36.0（CI 编译配置）构建与 30 条声明三公理白名单检查
lake exe cache get
lake build OnePlusOne
lake env lean AxiomsCheckOnePlusOne.lean

# 3. Comparator 独立多内核导出复核（leanchecker-paranoid + nanoda_bin + sorryAx 自挑战拒斥）
bash comparator/run_comparator.sh
```

---

## 3. 主要源码核查索引

| 核查模块 | 上游路径 |
|---|---|
| 顶层导出定理 | `1+1/OnePlusOne/Main.lean` |
| 显式外部解析前提接口（零 `axiom`） | `1+1/OnePlusOne/External/Premises.lean` |
| 初等算术与筛法核心引理（无条件 Lean 证明） | `1+1/OnePlusOne/Arithmetic/ElementaryBounds.lean` |
| 定理 1A 二进折半全范围收口（无条件 Lean 证明） | `1+1/OnePlusOne/Exceptional/DyadicClosure.lean` |
| 定理 1B 小区间补空与 Fejér 正性归约 | `1+1/OnePlusOne/ShortInterval/FejerReduction.lean` |
| 定理 3 构造性二进制桥梁 $48 \le N \le 1.934\cdot 10^{25}$ | `1+1/OnePlusOne/Linnik/Reduction.lean` |
| 独立 Comparator 挑战目标声明 | `1+1/comparator/ChallengeOnePlusOneReduction.lean` |
| 数学推导与证明边界详细说明 | `1+1/notes/DESIGN_AND_PROOF_SPEC.md`、`1+1/notes/LINNIK_GOLDBACH_SPEC.md` |
