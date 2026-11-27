import Mathlib

open scoped BigOperators

private theorem sum_divisors_reindex {M : Type*} [AddCommMonoid M]
    (n U B : ℕ) (F : ℕ → ℕ → ℕ → M) :
    (∑ m ∈ Finset.range (n + 1),
        ∑ a ∈ (Nat.divisors m).filter (fun a => U < a ∧ a ≤ B ∧ U < m / a),
          F m a (m / a)) =
      ∑ a ∈ Finset.Icc (U + 1) B,
        ∑ r ∈ Finset.Icc (U + 1) (n / a), F (a * r) a r := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 / x.2⟩) (fun x => ⟨x.1 * x.2, x.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hm, ha⟩
    rcases Finset.mem_filter.mp ha with ⟨hadiv, hUa, haB, hUr⟩
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · dsimp only
      exact Finset.mem_Icc.mpr ⟨by omega, haB⟩
    · dsimp only
      refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
      exact Nat.div_le_div_right (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨ha, hr⟩
    rcases Finset.mem_Icc.mp ha with ⟨hUa, haB⟩
    rcases Finset.mem_Icc.mp hr with ⟨hUr, hrn⟩
    have ha0 : 0 < x.1 := by omega
    have hprod : x.1 * x.2 ≤ n := by
      have h1 : x.2 * x.1 ≤ n := (Nat.le_div_iff_mul_le ha0).1 hrn
      rwa [Nat.mul_comm] at h1
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · dsimp only
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hprod)
    · dsimp only
      refine Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr
           ⟨Nat.dvd_mul_right x.1 x.2, Nat.mul_ne_zero (by omega) (by omega)⟩,
          by omega, haB, ?_⟩
      rw [Nat.mul_div_cancel_left x.2 ha0]
      omega
  · intro x hx
    dsimp only
    rcases Finset.mem_sigma.mp hx with ⟨hm, ha⟩
    rcases Finset.mem_filter.mp ha with ⟨hadiv, hcut⟩
    have hdvd : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hadiv
    rw [Nat.mul_div_cancel' hdvd]
    all_goals rfl
  · intro x hx
    dsimp only
    rcases Finset.mem_sigma.mp hx with ⟨ha, hr⟩
    rcases Finset.mem_Icc.mp ha with ⟨hUa, haB⟩
    have ha0 : 0 < x.1 := by omega
    rw [Nat.mul_div_cancel_left x.2 ha0]
    all_goals rfl
  · intro x hx
    dsimp only
    rcases Finset.mem_sigma.mp hx with ⟨hm, ha⟩
    rcases Finset.mem_filter.mp ha with ⟨hadiv, hcut⟩
    have hdvd : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hadiv
    rw [Nat.mul_div_cancel' hdvd]
    all_goals rfl

theorem Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion :
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ArithmeticFunction.vonMangoldt (m / a); ∀ (n : ℕ) (t : ℝ), S n (τ₁ n) t = ∑ a ∈ Finset.Icc (U n + 1) (B₁ n), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ∑ r ∈ Finset.Icc (U n + 1) (n / a), ArithmeticFunction.vonMangoldt r * E (((a*r:ℕ):ℝ)*t)
    := by
  intro E S U B₁ μ τ₁ n t
  classical
  have hS : S = fun (m : ℕ) (u : ℕ → ℝ) (s : ℝ) =>
      Finset.sum (Finset.range (m + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * s)) := rfl
  have hτ : τ₁ = fun (m k : ℕ) =>
      ∑ a ∈ (Nat.divisors k).filter (fun a => U m < a ∧ a ≤ B₁ m ∧ U m < k / a),
        (∑ d ∈ (Nat.divisors a).filter (fun d => U m < d), μ d) *
          ArithmeticFunction.vonMangoldt (k / a) := rfl
  set c : ℕ → ℝ := fun a => ∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d with hc
  set F : ℕ → ℕ → ℕ → ℂ := fun m a r =>
    ((c a * ArithmeticFunction.vonMangoldt r : ℝ) : ℂ) * E ((m : ℝ) * t) with hF
  calc
    S n (τ₁ n) t
        = ∑ m ∈ Finset.range (n + 1),
            ∑ a ∈ (Nat.divisors m).filter
                (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), F m a (m / a) := by
      simp only [hS, hτ, hF, hc, Complex.ofReal_sum, Finset.sum_mul]
    _ = ∑ a ∈ Finset.Icc (U n + 1) (B₁ n),
          ∑ r ∈ Finset.Icc (U n + 1) (n / a), F (a * r) a r :=
      sum_divisors_reindex n (U n) (B₁ n) F
    _ = ∑ a ∈ Finset.Icc (U n + 1) (B₁ n),
          (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) *
            ∑ r ∈ Finset.Icc (U n + 1) (n / a),
              ArithmeticFunction.vonMangoldt r * E (((a * r : ℕ) : ℝ) * t) := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      simp only [hF, hc, Complex.ofReal_mul]
      ring
