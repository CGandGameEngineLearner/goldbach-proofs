# Binary-shift exceptions and the signed middle-arc coefficient

For an integer scale $X$, let $E(X)$ consist of the even $n$ in $[X,2X)$ for which at least one shift $n-2^e$, with $1\le e\le\lfloor(\log_2X)/2\rfloor$, has no representation as a sum of two primes. The target of `L-goldbach-binary-shift-exception-union` is $|E(X)|^5\le X^4$ for all sufficiently large $X$.

The Lean theorem `Goldbach.JointSignedResidual.frozen_of_stripped_pairs` reduces that target to a lower-tail estimate for one complex Fourier coefficient. The lower-tail estimate remains open. [Terminal theorem](StrippedResidualTerminal.lean) · [Build and replay](BUILD.md) · [Lean axiom output](checked-axioms.txt)

## The estimate that suffices

At integer scale $Y$, set $L=\lfloor\log_2(Y+2)\rfloor$, $Q=\lfloor Y^{1/3}\rfloor$ and $H=256QL^2$. For each reduced $a/q$ with $L^2<q<Y^{1/4}$ and $q\le Q$, take the window $|\beta|\le H/(qY)$, where $\beta=t-a/q$. Write $c=\mu(q)/\varphi(q)$ and $K_Y(\beta)=\sum_{k=0}^{Y}e^{2\pi i k\beta}$. Let $Z$ be the project's `GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β`.

For sufficiently large $Y$ these windows are disjoint. On them define $R_Y=Z^2-2cK_YZ$, and set $R_Y=0$ outside them. Write $\widehat R_Y(m)=\int_0^1 R_Y(t)e^{-2\pi i m t}\,dt$. The square $Z^2$ and the negative Fourier phase both enter the real part in the following test. [Window formula](SignedRowOffsetRemoval.lean)

Fix real $\alpha<4/5$ and $C>0$. Suppose that for every sufficiently large integer $X$ at most $CX^{1+\alpha}$ integer pairs $(Y,m)$ satisfy all three conditions below.

1. $m$ is even and $\lfloor X/2\rfloor\le m\le 2X$.
2. $\lceil 2m/3\rceil\le Y\le\lfloor 3m/4\rfloor$.
3. $\operatorname{Re}\widehat R_Y(m)<-Y/256$.

Then $|E(X)|^5\le X^4$ for every sufficiently large $X$. The hypothesis counts pairs, so a frequency that fails at several interior scales contributes once per failing scale.

## Verified estimates

| Step | What is proved | Lean source |
| --- | --- | --- |
| Low denominators | For large $Y$ and even $Y\le m\le 3Y/2$, the real part of the true coefficient on the full $q\le L^2$ windows is at least $7Y/64$. | [Low-window estimate](ShiftSignedCommonLow.lean) |
| Model comparison | Replacing the true middle-window coefficient by the zero-corrected one costs at most $108\cdot128^2X^{5/3}$ additional failing pairs when the threshold changes from $-Y/64$ to $-Y/128$. Both coefficients may be centered at the same complex value. | [Dyadic pair count](CanonicalDyadicPairs.lean) |
| Constant mode | The geometric kernel starts at index zero. Removing all resulting offsets changes each Fourier coefficient by at most $Y^{2/3}$ for all sufficiently large $Y$, uniformly in $m$. This leaves $Z^2-2cK_YZ$ and allows the threshold $-Y/256$. | [Offset estimate](SignedRowOffsetRemoval.lean) · [Threshold transfer](CorrectionTransfer.lean) |
| Character sums | On summing over the reduced numerators, a linear Gauss factor vanishes unless the conductor of $\chi$ divides $q/\gcd(q,m)$. The quadratic factor obeys the same test for $\chi\psi$. For $m>0$ the remaining factors have explicit conductor and divisor-sum bounds. | [Contraction](CanonicalCharacterContraction.lean) · [Amplitude bounds](B13SignedAmplitudes.lean) |
| Low zeros and resonances | For fixed $K>0$ there is a $\delta>0$ for which near-one zeros of nonprincipal characters with conductor and height at most $X^\delta$ contribute zero in the strip $\operatorname{Re}z\ge1-K/\log X$. The principal character retains its zeta term. A separate count bounds individual resonances $r\mid hm$ for $r\ge X^\theta$ by $X^{1-\theta+\varepsilon}$ for fixed $h>0$ in the stated polynomial ranges. | [Zero removal](CanonicalLowConductorZerosActual.lean) · [Conductor incidences](ConductorIncidenceTerminal.lean) |

The outstanding step is to bound the negative real part after summing and integrating the surviving linear and quadratic terms. The conductor restriction holds term by term. Obtaining the pair count above requires additional control on their combined contribution.

## Upstream sources

- The reflected model supplies the rational-window geometry, the kernel and the truncated principal coefficient. The Estermann module and the unconditional deep second moment supply the prime estimates and outer-arc bounds. [Three-quarters model, PR #3709](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3709) · [Estermann almost-all, PR #3615](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3615) · [Deep second moment](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/1fe24b28926cd452b7a35f71ae1fc1cb82e01e84/lean/PEqualNP/Outside/L_goldbach_frontier_uncond_deep_second_moment.lean)
- The short-progression theorem supplies the input to the low-skirt argument on full windows. The exceptional-zero criterion supplies the actual signed Mellin correction used throughout. [Short progressions, PR #3789](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3789) · [Low-skirt reduction](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/1fe24b28926cd452b7a35f71ae1fc1cb82e01e84/lean/Conjectures/Goldbach/LowSkirtFromShortProgressions.lean) · [Exceptional-zero criterion](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/1fe24b28926cd452b7a35f71ae1fc1cb82e01e84/lean/Conjectures/Goldbach/DeepThreeQuartersExceptionalZeroCriterion.lean)
- The amplitude bounds reuse the induced Gauss-sum estimates from the B13 argument. The low-zero result also uses the project's density and real-zero estimates. Source versions and hashes are recorded for replay. [B13 Gauss estimates](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/0b4bd06b3b9bf3c35c8bb52f961744e31552e3f2/lean/Conjectures/Goldbach/B13NondividingResidueReduction.lean) · [Pinned source hashes](sources.json)

For another treatment of the original shift-union problem via an ordinary exceptional-set estimate, see [muoshuosha's checkpoint, PR #3793](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3793).
