# 中模裙边所需的 Dirichlet L 函数零点排除定理

建议为 [`L-goldbach-frontier-skirt-medium-moduli`](https://www.movan.tech/goldbach/api/task?lemma=L-goldbach-frontier-skirt-medium-moduli) 引入已形式化的无条件零点排除定理。上游入口是 `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`。它适用于任意正模数及任意复值 Dirichlet 特征，在 `7 / 8 < s.re` 时排除零点，主特征在 `s = 1` 的极点单独处理。[固定版本的 Lean 源码](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)

## 下游用途

把中模裙边和式的显式公式模型分成主项、实部小于 `13 / 14` 的零点项及其余零点项。上游定理排除最后一类零点，因为 `7 / 8 < 13 / 14`。对主特征，模型使用在 `s = 1` 处去掉极点的函数。附带的 Lean 适配证明处理了这个点，并把上游的精确声明转为模型需要的非消失结论。[可独立核对的 Lean 适配](../reference-proofs/DirichletSevenEighthsSkirt.lean)

在本地的中模裙边组合证明中，适配后的零点排除足以完成近 1 零点模型的实部下界。仍需独立证明显式公式的截断与低频误差，以及其余零点项的平方积分估计。

## 导入请求

请维护者评估是否可以把上述上游定理迁移为项目的受信任依赖，或核验并登记表达同一结论的现有模块。上游固定版本采用 Lean 4.34.1，本项目采用 Lean 4.36.0。附带证明在本项目固定的工具链下核对的是使用端，直接移植上游证明还需要核验上游传递依赖和公理，并在本项目工具链上重新构建。[上游工具链](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/lean-toolchain)
