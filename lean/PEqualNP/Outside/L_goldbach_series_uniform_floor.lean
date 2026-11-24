import Mathlib

open scoped BigOperators

private lemma comparisonFactor_nonneg {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ 1 - 1 / (k : ℝ) ^ 2 := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hksq : 1 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hle : 1 / (k : ℝ) ^ 2 ≤ 1 :=
    (div_le_one (by positivity)).mpr hksq
  linarith

private lemma comparisonFactor_le_one (k : ℕ) :
    1 - 1 / (k : ℝ) ^ 2 ≤ 1 := by
  have : 0 ≤ 1 / (k : ℝ) ^ 2 := by positivity
  linarith

private lemma comparisonProduct_Icc (Q : ℕ) (hQ : 2 ≤ Q) :
    (∏ k ∈ Finset.Icc 2 Q, (1 - 1 / (k : ℝ) ^ 2)) =
      ((Q : ℝ) + 1) / (2 * (Q : ℝ)) := by
  induction Q, hQ using Nat.le_induction with
  | base => norm_num
  | succ Q hQ ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      have hQ0 : (Q : ℝ) ≠ 0 := by positivity
      have hQ1 : (Q : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      push_cast
      ring

namespace PEqualNP.Outside

theorem L_goldbach_series_uniform_floor :
    let fac := fun p n : ℕ => if p ∣ n then (p:ℝ)/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2; let P := fun Q : ℕ => (Finset.range (Q+1)).filter (fun p => Nat.Prime p ∧ 2<p); ∀ Q n, 1 ≤ 2*Finset.prod (P Q) (fun p => fac p n) := by
  dsimp only
  intro Q n
  let P : Finset ℕ := (Finset.range (Q + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)
  let g : ℕ → ℝ := fun k => 1 - 1 / (k : ℝ) ^ 2
  let fac : ℕ → ℝ := fun p =>
    if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) else g (p - 1)
  change 1 ≤ 2 * ∏ p ∈ P,
    (if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)
  have hfac_ge : ∀ p ∈ P, g (p - 1) ≤ fac p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpRange, hpprime, hpgt⟩
    have hp3 : 3 ≤ p := hpgt
    have hp1 : 1 ≤ p := by omega
    have hden : 0 < (p : ℝ) - 1 := by
      have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp1]
      norm_num
    by_cases hdiv : p ∣ n
    · have hdiff :
          (p : ℝ) / ((p : ℝ) - 1) - g (p - 1) =
            (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        simp only [g, hcast]
        field_simp [hden.ne']
        ring
      have hpos : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
      change g (p - 1) ≤ (if p ∣ n then
        (p : ℝ) / ((p : ℝ) - 1) else g (p - 1))
      rw [ite_eq_left hdiv]
      linarith
    · change g (p - 1) ≤ (if p ∣ n then
        (p : ℝ) / ((p : ℝ) - 1) else g (p - 1))
      rw [ite_eq_right hdiv]
  have hbase_nonneg : ∀ k ∈ Finset.Icc 2 Q, 0 ≤ g k := by
    intro k hk
    exact comparisonFactor_nonneg (Finset.mem_Icc.mp hk).1
  have hbase_le_one : ∀ k ∈ Finset.Icc 2 Q, g k ≤ 1 := by
    intro k hk
    exact comparisonFactor_le_one k
  have hsubset : P.image (fun p => p - 1) ⊆ Finset.Icc 2 Q := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    rcases Finset.mem_filter.mp hp with ⟨hpRange, hpprime, hpgt⟩
    have hpQ : p ≤ Q := by
      have := Finset.mem_range.mp hpRange
      omega
    rw [Finset.mem_Icc]
    omega
  have hinj : Set.InjOn (fun p : ℕ => p - 1) P := by
    intro p hp q hq hpq
    rcases Finset.mem_filter.mp hp with ⟨_, _, hpgt⟩
    rcases Finset.mem_filter.mp hq with ⟨_, _, hqgt⟩
    change p - 1 = q - 1 at hpq
    omega
  have hIcc : (1 / 2 : ℝ) ≤ ∏ k ∈ Finset.Icc 2 Q, g k := by
    by_cases hQ : 2 ≤ Q
    · rw [show (∏ k ∈ Finset.Icc 2 Q, g k) =
          ((Q : ℝ) + 1) / (2 * (Q : ℝ)) by
        exact comparisonProduct_Icc Q hQ]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [show (0 : ℝ) ≤ (Q : ℝ) by positivity]
    · have hPempty : P = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpRange, hpprime, hpgt⟩
        have hpQ : p ≤ Q := by
          have := Finset.mem_range.mp hpRange
          omega
        omega
      have hIccEmpty : Finset.Icc 2 Q = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkQ : k ≤ Q := (Finset.mem_Icc.mp hk).2
        omega
      rw [hIccEmpty, Finset.prod_empty]
      norm_num
  have hprod_ge : (1 / 2 : ℝ) ≤ ∏ p ∈ P, fac p := by
    calc
      (1 / 2 : ℝ) ≤ ∏ k ∈ Finset.Icc 2 Q, g k := hIcc
      _ ≤ ∏ k ∈ P.image (fun p => p - 1), g k :=
        Finset.prod_le_prod_of_subset_of_le_one₀ hsubset hbase_nonneg
          (fun k hk hks => hbase_le_one k hk)
      _ = ∏ p ∈ P, g (p - 1) := by
        rw [Finset.prod_image]
        exact hinj
      _ ≤ ∏ p ∈ P, fac p := by
        apply Finset.prod_le_prod₀
        · intro p hp
          rcases Finset.mem_filter.mp hp with ⟨_, _, hpgt⟩
          exact comparisonFactor_nonneg (by omega)
        · exact hfac_ge
  have hprod_eq : (∏ p ∈ P, fac p) = ∏ p ∈ P,
      (if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    apply Finset.prod_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, _, hpgt⟩
    have hp1 : 1 ≤ p := by omega
    simp only [fac, g]
    rw [show ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 by
      rw [Nat.cast_sub hp1]
      norm_num]
  have hprod_ge_direct : (1 / 2 : ℝ) ≤ ∏ p ∈ P,
      (if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [← hprod_eq]
    exact hprod_ge
  linarith

end PEqualNP.Outside
