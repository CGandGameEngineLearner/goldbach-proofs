import Mathlib

open scoped BigOperators

namespace FourResidueProduct

private noncomputable def factor (n p : ℕ) : ℝ :=
  (1 - ([(0 : ℕ), p - 2, n % p, (n + 2) % p].toFinset.card : ℝ) / (p : ℝ)) /
    (1 - 1 / (p : ℝ)) ^ 4

private noncomputable def shape (p : ℝ) : ℝ := ((p - 4) / (p - 1)) ^ 2

private theorem factor_min (n p : ℕ) (hp : 5 ≤ p) :
    ((p : ℝ) - 4) * (p : ℝ)^3 / ((p : ℝ) - 1)^4 ≤ factor n p := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hc : ([(0 : ℕ), p - 2, n % p, (n + 2) % p].toFinset.card : ℝ) ≤ 4 := by
    exact_mod_cast (show [(0 : ℕ), p - 2, n % p, (n + 2) % p].toFinset.card ≤ 4 from
      List.toFinset_card_le _)
  have h0 : (0 : ℝ) < p := by linarith
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  unfold factor
  calc
    _ = (1 - 4 / (p : ℝ)) / (1 - 1 / (p : ℝ))^4 := by
      rw [show (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) by field_simp]
      field_simp
    _ ≤ _ := by gcongr

private theorem shape_step (p : ℝ) (hp : 5 ≤ p) :
    shape p ≤ (((p - 4) * p^3) / (p - 1)^4) * shape (p+1) := by
  have h0 : 0 < p := by linarith
  have h1 : 0 < p - 1 := by linarith
  have h4 : 0 ≤ p - 4 := by linarith
  have heq : p * (p-3)^2 - (p-4)*(p-1)^2 = 4 := by ring
  unfold shape
  rw [show p + 1 - 4 = p - 3 by ring, show p + 1 - 1 = p by ring]
  rw [div_pow, div_pow]
  have hpower : 0 < (p-1)^4 := by positivity
  have hpower2 : 0 < (p-1)^2 := by positivity
  have hpower3 : 0 < p^2 := by positivity
  rw [div_mul_div_comm, div_le_div_iff₀ hpower2 (mul_pos hpower hpower3)]
  have hpos : 0 ≤ 4 * ((p-4) * p^2 * (p-1)^2) := by positivity
  have hh : (p-4)^2 * ((p-1)^4 * p^2) -
      ((p-4) * p^3 * (p-3)^2) * (p-1)^2 = -(4 * ((p-4) * p^2 * (p-1)^2)) := by
    linear_combination -((p-4) * p^2 * (p-1)^2) * heq
  linarith only [hh, hpos]

private theorem shape_le_one (p : ℝ) (hp : 5 ≤ p) : shape p ≤ 1 := by
  have hn : 0 ≤ (p-4)/(p-1) := div_nonneg (by linarith) (by linarith)
  have hu : (p-4)/(p-1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  unfold shape
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) hn]

private theorem shape_mono_step (p : ℝ) (hp : 5 ≤ p) : shape p ≤ shape (p+1) := by
  have ha : 0 < p - 1 := by linarith
  have hb : 0 < p := by linarith
  have h₁ : 0 ≤ (p-4)/(p-1) := div_nonneg (by linarith) ha.le
  have h₂ : (p-4)/(p-1) ≤ (p+1-4)/(p+1-1) := by
    rw [show p+1-1=p by ring, div_le_div_iff₀ ha hb]
    nlinarith
  exact pow_le_pow_left₀ h₁ h₂ _

private noncomputable def part (n z : ℕ) : ℝ :=
  ∏ p ∈ Finset.Ico 5 z, if p.Prime then factor n p else 1

private theorem part_step (n p : ℕ) (hp : 5 ≤ p) :
    part n (p+1) = part n p * (if p.Prime then factor n p else 1) := by
  exact Finset.prod_Ico_succ_top hp _

private theorem part_lower (n z : ℕ) : (3 / 32 : ℝ) ≤ part n z := by
  have h5 : (125 / 256 : ℝ) ≤ factor n 5 := by
    have h := factor_min n 5 (by decide)
    norm_num at h ⊢
    exact h
  have ha : part n 5 = 1 := by simp [part]
  have hb : part n 6 = factor n 5 := by
    rw [show (6 : ℕ) = 5+1 by decide, part_step n 5 (by decide), ha]
    simp [Nat.prime_five]
  have hc : part n 7 = factor n 5 := by
    rw [show (7 : ℕ) = 6+1 by decide, part_step n 6 (by decide), hb]
    simp [show ¬ Nat.Prime 6 by decide]
  by_cases hz : z < 7
  · rcases lt_or_ge z 5 with h | h
    · have hempty : Finset.Ico 5 z = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have := Finset.mem_Ico.mp hx
        omega
      simp [part, hempty]
      norm_num
    · have hcases : z = 5 ∨ z = 6 := by omega
      rcases hcases with rfl | rfl
      · rw [ha]; norm_num
      · rw [hb]; linarith
  have prop : ∀ j : ℕ, (3/32 : ℝ) ≤ part n (7+j) * shape (↑(7+j : ℕ)) := by
    intro j
    induction j with
    | zero =>
      simpa only [Nat.add_zero, hc] using
        (show (3/32 : ℝ) ≤ factor n 5 * shape (↑(7 : ℕ) : ℝ) by
          norm_num [shape]; linarith)
    | succ j ih =>
      let p := 7+j
      have hp : 5 ≤ p := by dsimp [p]; omega
      have hp' : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      change (3/32 : ℝ) ≤ part n (p+1) * shape (↑(p+1 : ℕ))
      change (3/32 : ℝ) ≤ part n p * shape (p : ℝ) at ih
      have hn : 0 ≤ part n p := by
        by_contra! hneg
        have := mul_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg (((p : ℝ)-4)/((p : ℝ)-1)))
        exact (not_le_of_gt (by norm_num : (0 : ℝ) < 3/32)) (ih.trans this)
      rw [part_step n p hp, Nat.cast_add, Nat.cast_one, mul_assoc]
      apply ih.trans (mul_le_mul_of_nonneg_left ?_ hn)
      split
      · exact (shape_step _ hp').trans
          (mul_le_mul_of_nonneg_right (factor_min n p hp) (sq_nonneg _))
      · rw [one_mul]
        exact shape_mono_step _ hp'
  have h := prop (z-7)
  rw [show 7 + (z-7) = z by omega] at h
  have hz' : (5 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 5 ≤ z by omega)
  have hn : 0 ≤ part n z := by
    by_contra! hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg (((z : ℝ)-4)/((z : ℝ)-1)))
    exact (not_le_of_gt (by norm_num : (0 : ℝ) < 3/32)) (h.trans this)
  exact h.trans (mul_le_of_le_one_right hn (shape_le_one _ hz'))

end FourResidueProduct

theorem Conjectures.Cuts.Task2e34a47e0a2430353f1bc6b5 : (have x1 : ℕ → ℕ → ℝ := fun (x1 x2 : ℕ) => (27 / 2 : ℝ) * (∏ x3 ∈ Finset.Ico (5 : ℕ) x1 with Nat.Prime x3, ((1 : ℝ) - (↑[(0 : ℕ), x3 - (2 : ℕ), x2 % x3, (x2 + (2 : ℕ)) % x3].toFinset.card : ℝ) / (↑x3 : ℝ)) / ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ)) ^ (4 : ℕ)); ∀ (x2 x3 : ℕ), x3 % (6 : ℕ) = (4 : ℕ) → (81 / 64 : ℝ) ≤ x1 x2 x3) := by
  dsimp only
  intro z n _
  change (81 / 64 : ℝ) ≤ (27 / 2 : ℝ) *
    (∏ p ∈ (Finset.Ico 5 z).filter Nat.Prime, FourResidueProduct.factor n p)
  rw [Finset.prod_filter]
  have h := FourResidueProduct.part_lower n z
  change (3 / 32 : ℝ) ≤ ∏ p ∈ Finset.Ico 5 z, (if p.Prime then FourResidueProduct.factor n p else 1) at h
  linarith
