import Mathlib

/-!
# Cut: two-sided prime-power reduction of the frozen tau_3 x tau_3 deep floor

Parent: `L-goldbach-frontier-type2-b3-b3-parity`. The frozen statement asks for the one-sided
deep-minor bound `-(e*n) <= Re Jdeep n (tau_3 n) (tau_3 n)` for even `n`. The cut replaces the
von Mangoldt coefficient `tau_3` first by its prime-only version `P` and then by the
small-prime-truncated prime-only version `Pp` (inner prime above `n^(7/24)`), charging both
replacements an `o(n)` error. What remains is the signed floor for the restricted coefficient
`Pp`, whose products carry at most three distinct inner primes, each above `n^(7/24)`.

Sources: `notes/type2-prime-power-reduction.md` (proper prime powers: divisor support counting
plus Parseval exponents `n^(11/12+o(1))` and `n^(47/48+o(1))`),
`notes/type2-b3-reduced-signed-target.md` (the restricted target this cut isolates) and
`notes/type2-b3-odd-support-obstruction.md` (why no absolute-value or parity argument can
replace the signed floor: the reflection identity asks for a symmetric-versus-antisymmetric
deep energy comparison, which is exactly the residual obstruction left in child 3).

The combination is the triangle inequality. With `A`, `B`, `C` the three real parts,
`|A-B| <= e/3*n`, `|B-C| <= e/3*n` and `C >= -e/3*n` give `A >= -e*n`.
-/

-- child 1 zh: 用素数处取 log、其余为零的系数 P 替换 von Mangoldt 系数 τ₃，深积分实部误差为 o(n)（真素数幂支撑计数 O(n^(11/12+o(1)))，由除数支撑计数加 Parseval 得到）。
-- child 1 en: Replacing the von Mangoldt coefficient tau_3 by the prime-only coefficient P (log at primes, zero elsewhere) changes the real part of the deep integral by o(n); proper prime powers contribute O(n^(11/12+o(1))) by divisor support counting plus Parseval.
-- child 2 zh: 再把素数系数的内层素数限制到大于 n^(7/24)，深积分实部误差仍为 o(n)（被弃支撑 ≤ n^(23/24)，得到 O(n^(47/48+o(1)))）。
-- child 2 en: Restricting the prime-only coefficient to inner primes above n^(7/24) changes the real part of the deep integral by o(n) again; the discarded support has at most n^(23/24) elements and costs O(n^(47/48+o(1))).
-- child 3 zh: 受限素数系数 Pp 的深带符号单边下界：每个乘积至多含三个不同内层素数且都大于 n^(7/24)，仍须满足冻结的实部下界；这是奇支撑反例之后剩下的真实带符号抵消核心。
-- child 3 en: The signed one-sided floor for the restricted prime-only coefficient Pp: at most three distinct inner primes per product, each above n^(7/24). This is the surviving signed-cancellation core after the prime-power and small-prime reductions; the odd-support counterexample shows it cannot be replaced by any absolute-value or parity statement.
theorem Conjectures.Cuts.Cut1f1c5f0de64ba5a4ca8ea190
    (h₁ : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume;
      let P := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * (if Nat.Prime (m / a) then Real.log (m / a) else 0);
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        |(Jdeep n (τ₃ n) (τ₃ n)).re - (Jdeep n (P n) (P n)).re| ≤ eps * (n : ℝ))
    (h₂ : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume;
      let V := fun n : ℕ => ⌊(n:ℝ)^(7/24:ℝ)⌋₊; let P := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * (if Nat.Prime (m / a) then Real.log (m / a) else 0);
      let Pp := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a ∧ V n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * (if Nat.Prime (m / a) then Real.log (m / a) else 0);
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        |(Jdeep n (P n) (P n)).re - (Jdeep n (Pp n) (Pp n)).re| ≤ eps * (n : ℝ))
    (h₃ : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume;
      let V := fun n : ℕ => ⌊(n:ℝ)^(7/24:ℝ)⌋₊; let Pp := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a ∧ V n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * (if Nat.Prime (m / a) then Real.log (m / a) else 0);
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        -(eps * (n : ℝ)) ≤ (Jdeep n (Pp n) (Pp n)).re)
    :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (Jdeep n (τ₃ n) (τ₃ n)).re) := by
  -- Purely real step: two o(n) replacements plus the o(n) floor of the reduced coefficient
  -- give the o(n) floor of the parent coefficient.
  have key : ∀ (A B C : ℝ) (e : ℝ) (n : ℕ), |A - B| ≤ e/3 * (n:ℝ) →
      |B - C| ≤ e/3 * (n:ℝ) → -(e/3 * (n:ℝ)) ≤ C → -(e * (n:ℝ)) ≤ A := by
    intro A B C e n hab hbc hc
    have h1 : -(e/3 * (n:ℝ)) ≤ A - B := (abs_le.mp hab).1
    have h2 : -(e/3 * (n:ℝ)) ≤ B - C := (abs_le.mp hbc).1
    have h3 : (e/3 * (n:ℝ)) * 3 = e * (n:ℝ) := by ring
    linarith
  refine fun e he => ?_
  obtain ⟨N₁, hN₁⟩ := h₁ (e/3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := h₂ (e/3) (by linarith)
  obtain ⟨N₃, hN₃⟩ := h₃ (e/3) (by linarith)
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro n hn hEven
  have h1n := hN₁ n ((le_max_left N₁ N₂).trans (le_max_left (max N₁ N₂) N₃) |>.trans hn) hEven
  have h2n := hN₂ n ((le_max_right N₁ N₂).trans (le_max_left (max N₁ N₂) N₃) |>.trans hn) hEven
  have h3n := hN₃ n (le_max_right (max N₁ N₂) N₃ |>.trans hn) hEven
  exact key _ _ _ e n h1n h2n h3n
