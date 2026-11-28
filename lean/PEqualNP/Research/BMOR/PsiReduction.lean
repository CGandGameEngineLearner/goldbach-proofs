import Mathlib

namespace PEqualNP.Outside.PsiReduction

open ArithmeticFunction

noncomputable def psi (q a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), vonMangoldt k

/-- Every even prime power through n divides the greatest power of two through n. -/
theorem even_mass_le_log (n : ℕ) (hn : n ≠ 0) : psi 2 0 n ≤ Real.log n := by
  let t := 2 ^ Nat.log 2 n
  have ht : t ≠ 0 := by dsimp [t]; positivity
  have htn : t ≤ n := Nat.pow_log_le_self 2 hn
  have hlog : Real.log (t : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ht) (by exact_mod_cast htn)
  rw [← vonMangoldt_sum] at hlog
  apply le_trans _ hlog
  unfold psi
  rw [← Finset.sum_filter_ne_zero]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
  intro k hk
  obtain ⟨hkS, hΛ⟩ := Finset.mem_filter.mp hk
  obtain ⟨hkn, heven⟩ := Finset.mem_filter.mp hkS
  have hkn' : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hkn
  obtain ⟨p, e, hp, _, he⟩ := (isPrimePow_nat_iff k).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hd : 2 ∣ p ^ e := he ▸ Nat.dvd_of_mod_eq_zero heven
  have htwo : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow hd)
  subst p
  rw [← he] at hkn' ⊢
  exact Nat.mem_divisors.mpr ⟨pow_dvd_pow 2 ((Nat.le_log_iff_pow_le (by decide) hn).mpr hkn'), ht⟩

theorem psi_two (n a : ℕ) (ha : a.Coprime 2) :
    psi 2 a n = psi 4 1 n + psi 4 3 n := by
  have ha' : a % 2 = 1 := Nat.odd_iff.mp ha.odd_of_right
  simp only [psi, Finset.sum_filter, ha', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h₁ : k % 4 = 1 <;> by_cases h₃ : k % 4 = 3 <;>
    by_cases h₂ : k % 2 = 1 <;> first | omega | norm_num [h₁, h₃, h₂]

theorem psi_one (n a : ℕ) : psi 1 a n = psi 2 1 n + psi 2 0 n := by
  simp only [psi, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with h | h <;> norm_num [Nat.mod_one, h]

/-- The one-percent target for all moduli follows from an n/300 estimate for
the reduced representatives of moduli 3 through 105 at the same n. -/
theorem all_moduli_of_psi (n : ℕ) (hn : 10^16 ≤ n)
    (h : ∀ q r : ℕ, 3 ≤ q → q ≤ 105 → 1 ≤ r → r < q → r.Coprime q →
      |psi q r n - (n : ℝ) / Nat.totient q| ≤ (n : ℝ) / 300) :
    ∀ q a : ℕ, 1 ≤ q → q ≤ 105 → a.Coprime q →
      |psi q a n - (n : ℝ) / Nat.totient q| ≤ (n : ℝ) / 100 := by
  intro q a hq hq' ha
  by_cases hlarge : 3 ≤ q
  · have hr : (a % q).Coprime q := by
      change (a % q).gcd q = 1
      rwa [← Nat.gcd_rec, Nat.gcd_comm]
    have hrpos : 1 ≤ a % q := by
      by_contra! hlt
      have hz : a % q = 0 := by omega
      simp [hz] at hr
      omega
    have h' := h q (a % q) hlarge hq' hrpos (Nat.mod_lt _ (by omega)) hr
    have heq : psi q (a % q) n = psi q a n := by simp [psi]
    rw [heq] at h'
    exact h'.trans (by linarith [Nat.cast_nonneg (α := ℝ) n])
  · have h₁ := h 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h₃ := h 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [show Nat.totient 4 = 2 by decide] at h₁ h₃
    obtain ⟨h1lo, h1hi⟩ := abs_le.mp h₁
    obtain ⟨h3lo, h3hi⟩ := abs_le.mp h₃
    have hqsmall : q = 1 ∨ q = 2 := by omega
    rcases hqsmall with rfl | rfl
    · rw [psi_one, psi_two n 1 (by decide)]
      norm_num [Nat.totient_one]
      have hlo : 0 ≤ psi 2 0 n := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
      have hhi := even_mass_le_log n (by norm_num at hn; omega)
      have hn' : (10:ℝ)^16 ≤ n := by exact_mod_cast hn
      have hs : (10:ℝ)^8 ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by linarith)
      have hl := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt n by linarith)
      rw [Real.log_sqrt (by positivity)] at hl
      have hs2 := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
      have hsmall : Real.log n ≤ (n:ℝ)/300 := by
        nlinarith only [hl, hs2, mul_nonneg (Real.sqrt_nonneg (n:ℝ))
          (show 0 ≤ Real.sqrt n - 600 by linarith)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [psi_two n a ha]
      norm_num [Nat.totient_two]
      exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A coefficient of 1/10 in the scale n/log n suffices throughout FR-7022. -/
theorem all_moduli_of_normalized_estimate (n : ℕ) (hn : 10^16 ≤ n)
    (h : ∀ q r : ℕ, 3 ≤ q → q ≤ 105 → 1 ≤ r → r < q → r.Coprime q →
      |psi q r n - (n : ℝ) / Nat.totient q| ≤ (n : ℝ) / (10 * Real.log n)) :
    ∀ q a : ℕ, 1 ≤ q → q ≤ 105 → a.Coprime q →
      |psi q a n - (n : ℝ) / Nat.totient q| ≤ (n : ℝ) / 100 := by
  have hn' : (10 : ℝ)^16 ≤ n := by exact_mod_cast hn
  have hp : (2 : ℝ)^50 ≤ n := le_trans (by norm_num : (2 : ℝ)^50 ≤ 10^16) hn'
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at hl
  have hlog : 30 ≤ Real.log (n : ℝ) := by
    norm_num at hl
    linarith [Real.log_two_gt_d9]
  apply all_moduli_of_psi n hn
  intro q r hq hQ hr hrq ha
  apply (h q r hq hQ hr hrq ha).trans
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)

end PEqualNP.Outside.PsiReduction
