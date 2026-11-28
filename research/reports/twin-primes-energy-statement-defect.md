## 摘要 / Summary

`L-twin-primes-energy-bridge` 和 `L-twin-primes-prescribed-energy` 目前登记的陈述无法通过平台验证器。验证器在检查证明之前就以 `REJECTED (statement)` 退回，所以这两条的任何证明都不会被接受。`L-twin-primes-endpoint` 依赖前者，这条路线也因此卡住。问题出在陈述的写法，不在数学内容。

The registered statements of `L-twin-primes-energy-bridge` and `L-twin-primes-prescribed-energy` cannot pass the platform checker. It returns `REJECTED (statement)` before it looks at any proof, so no proof of either lemma can be accepted. `L-twin-primes-endpoint` depends on the first one, so that route is blocked too. The problem is how the statements are written, not their mathematics.

本 PR 只做报告，不修改目录。
This PR is a report only. It does not change the catalogue.

## 原因 / Cause

两条陈述在定义 `energy` 时都写了：
Both statements define `energy` with:

```lean
letI : NeZero (N X) := ⟨by dsimp [N]; omega⟩
```

验证器 `lean/CheckLemma.lean` 会先自行 elaborate 登记的陈述。这段 tactic 证明会被 Lean 抽成辅助声明 `PEqualNPChecker.recorded._proof_1`，它不在固定版本的 Mathlib 或 `PEqualNP.Defs` 里，于是被第 231 行的规则退回：

The checker (`lean/CheckLemma.lean`) first elaborates the recorded statement itself. Lean turns this tactic proof into an auxiliary declaration, `PEqualNPChecker.recorded._proof_1`. That declaration is not in the pinned Mathlib or `PEqualNP.Defs`, so the rule at line 231 rejects the statement:

```
REJECTED (statement): the recorded statement rests on declarations that are not in the pinned library or the definitions root as the kernel accepted them: [PEqualNPChecker.recorded._proof_1]. Write it as one term that needs no auxiliary declaration
```

以上结果是在本地复现的，所用 `lean/CheckLemma.lean` 和 `tools/check-lean.mjs` 与 `main` 逐字相同。本地逐条 elaborate 四个题库的全部 47 条开放陈述后，只有这两条产生辅助声明。

We reproduced this locally with `lean/CheckLemma.lean` and `tools/check-lean.mjs` byte-identical to `main`. We also elaborated all 47 open statements across the four problem sets locally, and only these two produce an auxiliary declaration.

`main` 上出现的位置 / Locations on `main`:

- `research/problems.json` 第 5803 行（energy-bridge）和第 5873 行（prescribed-energy） / lines 5803 (energy-bridge) and 5873 (prescribed-energy)
- `research/problems/twin-primes/routes/06-theta-for-shift/tasks/L-twin-primes-energy-bridge.json`
- `research/problems/twin-primes/routes/06-theta-for-shift/tasks/L-twin-primes-prescribed-energy.json`

## 建议的修正 / Suggested fix

把 tactic 证明换成一个项，数学内容不变：
Replace the tactic proof with a term. The mathematics stays the same:

```lean
letI : NeZero (N X) := ⟨Nat.succ_ne_zero _⟩
```

`N X = 2*X+5` 可以与 `?n + 1` 统一，因此不会产生辅助声明。我们用同一份 energy-bridge 证明在本地测试：原陈述得到 `REJECTED (statement)`；换成上面的写法后得到 `ACCEPTED`，公理只有 `propext`、`Classical.choice`、`Quot.sound`。

`N X = 2*X+5` unifies with `?n + 1`, so no auxiliary declaration is created. With the same energy-bridge proof, our local checks gave `REJECTED (statement)` for the registered statement and `ACCEPTED` for the corrected one, using only `propext`, `Classical.choice` and `Quot.sound`.

不过已发布的陈述是冻结的。直接修改这两个任务文件后，`research/build_catalogue.py` 会报错：

Published statements are frozen, though. Editing the two task files in place makes `research/build_catalogue.py` fail with:

```
ValueError: Frozen statement changed: L-twin-primes-energy-bridge; create a new ID
```

因此需要维护者：
So a maintainer needs to:

1. 撤下这两个旧 ID。
   Retire the two old IDs.
2. 用新 ID（例如 `L-twin-primes-energy-bridge-v2`、`L-twin-primes-prescribed-energy-v2`）重新发布修正后的陈述，并在路线中注明替代关系。
   Republish the corrected statements under new IDs (for example `L-twin-primes-energy-bridge-v2` and `L-twin-primes-prescribed-energy-v2`), and note the replacement in the route.
3. 更新依赖：`L-twin-primes-endpoint` 改为依赖新的 energy-bridge，新的 energy-bridge 依赖新的 prescribed-energy。
   Update `depends_on`: `L-twin-primes-endpoint` should depend on the new energy-bridge, and the new energy-bridge on the new prescribed-energy.

具体做法由维护者决定。
How to carry this out is up to the maintainers.

## 参考 / References

- 完整说明 / Full write-up: https://github.com/dreyeki/gold/blob/9ab930d41fb966d670fbc91ba0bae59fe8ee248e/docs/energy-bridge-statement-defect.md
- 针对修正后陈述的 energy-bridge 证明 / Proof of energy-bridge for the corrected statement: https://github.com/dreyeki/gold/blob/9ab930d41fb966d670fbc91ba0bae59fe8ee248e/submissions/L_twin_primes_energy_bridge_fixed_statement.lean

本 PR 只新增这份报告，文件位于 `lean/PEqualNP/Outside/` 之外，不会触发证明检查。
This PR adds only this report. The file is outside `lean/PEqualNP/Outside/`, so no proof check runs.
