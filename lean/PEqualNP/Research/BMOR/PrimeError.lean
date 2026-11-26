import Mathlib

namespace PEqualNP.Outside.FixedAP

/-- The sum of log-prime weights for primes at most n in a residue class. -/
noncomputable def theta (q a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = a % q),
    if k.Prime then ArithmeticFunction.vonMangoldt k else 0

private theorem theta_two (n a : ℕ) (ha : a.Coprime 2) :
    theta 2 a n = theta 4 1 n + theta 4 3 n := by
  have ha' : a % 2 = 1 := Nat.odd_iff.mp ha.odd_of_right
  simp only [theta, Finset.sum_filter, ha', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h₁ : k % 4 = 1 <;> by_cases h₃ : k % 4 = 3 <;>
    by_cases h₂ : k % 2 = 1 <;> first | omega | norm_num [h₁, h₃, h₂]

private theorem theta_one (n a : ℕ) (hn : 2 ≤ n) :
    theta 1 a n = theta 2 1 n + Real.log 2 := by
  have hsingle : (∑ k ∈ Finset.range (n + 1), if k = 2 then Real.log 2 else 0) =
      Real.log 2 := by
    rw [Finset.sum_ite_eq']
    simp [Finset.mem_range, show 2 < n + 1 by omega]
  rw [← hsingle]
  simp only [theta, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hp : k.Prime
  · rcases hp.eq_two_or_odd with heq | hodd
    · subst k
      norm_num [Nat.mod_one, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    · have hk : k ≠ 2 := by omega
      simp [Nat.mod_one, hk, hodd, hp]
  · have hk : k ≠ 2 := fun h => hp (h ▸ Nat.prime_two)
    simp [hp, hk]

/-- A prime-weight BMOR input for standard reduced representatives and moduli 3 through
105 gives a uniform estimate for all reduced residue classes, including moduli 1 and 2. -/
theorem prime_error_of_bmor (n : ℕ) (hn : 10^16 ≤ n)
    (hBMOR : ∀ q r : ℕ, 3 ≤ q → q ≤ 105 → 1 ≤ r → r < q → r.Coprime q →
      |theta q r n - (n : ℝ) / Nat.totient q| ≤ (n : ℝ) / (840 * Real.log n)) :
    ∀ q a : ℕ, 1 ≤ q → q ≤ 105 → a.Coprime q →
      |theta q a n - (n : ℝ) / Nat.totient q| ≤ (n : ℝ) / 14000 := by
  have hnR : (10 : ℝ)^16 ≤ n := by exact_mod_cast hn
  have hlog : 35 ≤ Real.log (n : ℝ) := by
    have hpow : (2 : ℝ)^52 ≤ n := le_trans (by norm_num : (2 : ℝ)^52 ≤ 10^16) hnR
    have h := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at h
    norm_num at h
    linarith [Real.log_two_gt_d9]
  have hsmall : (n : ℝ) / (840 * Real.log n) ≤ n / 29400 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  intro q a hq hq' ha
  by_cases hlarge : 3 ≤ q
  · have hr : (a % q).Coprime q := by
      change (a % q).gcd q = 1
      rwa [← Nat.gcd_rec, Nat.gcd_comm]
    have hrpos : 1 ≤ a % q := by
      by_contra! h
      have hz : a % q = 0 := by omega
      simp [hz] at hr
      omega
    have h := hBMOR q (a % q) hlarge hq' hrpos (Nat.mod_lt _ (by omega)) hr
    have heq : theta q (a % q) n = theta q a n := by simp [theta]
    rw [heq] at h
    exact (h.trans hsmall).trans (by linarith)
  · have h₁ := (hBMOR 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsmall
    have h₃ := (hBMOR 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsmall
    have hφ : Nat.totient 4 = 2 := by decide
    rw [hφ] at h₁ h₃
    obtain ⟨h1lo, h1hi⟩ := abs_le.mp h₁
    obtain ⟨h3lo, h3hi⟩ := abs_le.mp h₃
    have hqsmall : q = 1 ∨ q = 2 := by omega
    rcases hqsmall with rfl | rfl
    · rw [theta_one n a (by norm_num at hn; omega), theta_two n 1 (by decide)]
      norm_num [Nat.totient_one]
      apply abs_le.mpr
      constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
    · rw [theta_two n a ha]
      norm_num [Nat.totient_two]
      apply abs_le.mpr
      constructor <;> linarith

end PEqualNP.Outside.FixedAP
