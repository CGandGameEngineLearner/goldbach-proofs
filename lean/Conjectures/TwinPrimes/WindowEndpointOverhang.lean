import Mathlib

set_option maxHeartbeats 1000000 in
theorem Conjectures.TwinPrimes.WindowEndpointOverhang :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
    ∀ (X : ℕ) (f : ℕ → ℝ) (A : ℝ), 2 ≤ X → 0 ≤ A →
      (∀ n : ℕ, n ≤ 2*X+2 → 0 ≤ f n ∧ f n ≤ A) →
      0 ≤ (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2)) ∧
      (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2)) ≤ 2*A^2 := by
  intro w X f A hX hA hf
  have hmem : ∀ n : ℕ, n ∈ w X ↔ (n < 2*X+1 ∧ X < n ∧ 50*n < 51*X) := by
    intro n
    simp only [w, Finset.mem_filter, Finset.mem_range]
  set W := w X with hWdef
  set g : ℕ → ℝ := fun n => f n * f (n+2) with hgdef
  set P : ℕ → Prop := fun n => n+2 ∈ W with hPdef
  have hs : (W.filter (fun n => ¬ P n)).sum g + (W.filter P).sum g = W.sum g := by
    have hs0 := Finset.sum_sdiff (s₁ := W.filter P) (s₂ := W) (f := g) (Finset.filter_subset P W)
    have he : W \ W.filter P = W.filter (fun n => ¬ P n) := by
      ext n
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      tauto
    rw [he] at hs0
    exact hs0
  have hdiff : W.sum g - (W.filter P).sum g = (W.filter (fun n => ¬ P n)).sum g := by
    linarith
  have hmemW : ∀ n ∈ W, n ≤ 2*X+2 ∧ n+2 ≤ 2*X+2 := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := (hmem n).mp hn
    omega
  have hg_nonneg : ∀ n ∈ W, 0 ≤ g n := by
    intro n hn
    obtain ⟨h1, h2⟩ := hmemW n hn
    exact mul_nonneg (hf n h1).1 (hf (n+2) h2).1
  have hg_le : ∀ n ∈ W, g n ≤ A^2 := by
    intro n hn
    obtain ⟨h1, h2⟩ := hmemW n hn
    obtain ⟨ha1, ha2⟩ := hf n h1
    obtain ⟨hb1, hb2⟩ := hf (n+2) h2
    calc g n = f n * f (n+2) := rfl
      _ ≤ A * A := mul_le_mul ha2 hb2 hb1 (le_trans ha1 ha2)
      _ = A^2 := by ring
  have hB_nonneg : 0 ≤ (W.filter (fun n => ¬ P n)).sum g := by
    refine Finset.sum_nonneg (fun n hn => hg_nonneg n ?_)
    exact (Finset.mem_filter.mp hn).1
  have hcard : (W.filter (fun n => ¬ P n)).card ≤ 2 := by
    have hsub : W.filter (fun n => ¬ P n) ⊆ Finset.Icc ((51*X - 51)/50) ((51*X - 1)/50) := by
      intro n hn
      obtain ⟨hnW, hnB⟩ := Finset.mem_filter.mp hn
      obtain ⟨h1, h2, h3⟩ := (hmem n).mp hnW
      have h5 : 51*X ≤ 50*(n+2) := by
        by_contra hc
        have hc' : 50*(n+2) < 51*X := by omega
        have hX2 : X < n + 2 := by omega
        exact hnB ((hmem (n+2)).mpr ⟨by omega, hX2, hc'⟩)
      have h6' : 50*n ≤ 51*X - 1 := Nat.le_pred_of_lt h3
      have h6 : n * 50 ≤ 51*X - 1 := by simpa [Nat.mul_comm] using h6'
      have hnM : n ≤ (51*X - 1)/50 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 50)).mpr h6
      have h5eq : 50*(n+2) = 50*n + 100 := by ring
      have h5' : 51*X ≤ 50*n + 100 := by rw [h5eq] at h5; exact h5
      have h7 : 51*X - 51 ≤ n * 50 + 50 - 1 := by omega
      have hnL : (51*X - 51)/50 ≤ n := (Nat.div_le_iff_le_mul (by norm_num : 0 < 50)).mpr h7
      exact Finset.mem_Icc.mpr ⟨hnL, hnM⟩
    have hcard : (Finset.Icc ((51*X - 51)/50) ((51*X - 1)/50)).card ≤ 2 := by
      have hkey : (51*X - 1) = (51*X - 51) + 50 * 1 := by omega
      have hstep : (51*X - 1)/50 = (51*X - 51)/50 + 1 := by
        rw [hkey, Nat.add_mul_div_left _ _ (by norm_num : 0 < 50)]
      rw [Nat.card_Icc, hstep]
      omega
    exact le_trans (Finset.card_le_card hsub) hcard
  constructor
  · rw [hdiff]
    exact hB_nonneg
  · rw [hdiff]
    have h2 : (W.filter (fun n => ¬ P n)).sum g ≤ ((W.filter (fun n => ¬ P n)).card : ℝ) * A^2 := by
      have hstep := Finset.sum_le_sum (f := g) (g := fun _ => A^2) (s := W.filter (fun n => ¬ P n))
        (fun n hn => hg_le n (Finset.mem_filter.mp hn).1)
      simpa [Finset.sum_const, nsmul_eq_mul] using hstep
    have h3 : ((W.filter (fun n => ¬ P n)).card : ℝ) * A^2 ≤ 2 * A^2 := by
      have hc : ((W.filter (fun n => ¬ P n)).card : ℝ) ≤ 2 := by exact_mod_cast hcard
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg A)
    linarith
