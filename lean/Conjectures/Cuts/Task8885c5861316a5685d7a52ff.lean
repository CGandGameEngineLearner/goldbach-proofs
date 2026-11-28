import Mathlib

theorem Conjectures.Cuts.Task8885c5861316a5685d7a52ff : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∀ (x2 : ℕ),   (16 : ℕ) ≤ x2 →     have x4 : ℕ := Nat.log (2 : ℕ) x2 / (2 : ℕ);     have x5 : Finset ℕ := {x5 ∈ Finset.Ico x2 ((2 : ℕ) * x2) | Even x5 ∧ (0 : ℕ) < {x6 ∈ Finset.Icc (1 : ℕ) x4 | x1 (x5 - (2 : ℕ) ^ x6) = (0 : ℕ)}.card};     x5.card ≤ x4 * {x6 ∈ Finset.Icc (4 : ℕ) ((2 : ℕ) * x2) | Even x6 ∧ x1 x6 = (0 : ℕ)}.card) := by
  intro reps X hX K bad
  let exponents := Finset.Icc 1 K
  let exceptions := (Finset.Icc 4 (2 * X)).filter fun m => Even m ∧ reps m = 0
  let pairs := exponents.product exceptions
  let target (p : ℕ × ℕ) := p.2 + 2 ^ p.1
  -- A failed shift at n gives the witness (k, n - 2^k) in this product.
  have cover : bad ⊆ pairs.image target := by
    intro n hn
    obtain ⟨hnI, hnEven, hfail⟩ := Finset.mem_filter.mp hn
    obtain ⟨hXn, hn2X⟩ := Finset.mem_Ico.mp hnI
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hfail
    obtain ⟨hkI, hzero⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hkI
    -- The exponent cutoff gives 2 * 2^k ≤ X, so the difference is at least 4.
    have hnext : k + 1 ≤ Nat.log 2 X := by
      change k ≤ Nat.log 2 X / 2 at hkK
      omega
    have hpow : 2 ^ k * 2 ≤ X := by
      rw [← pow_succ]
      exact (Nat.pow_le_pow_right (by decide : 0 < 2) hnext).trans
        (Nat.pow_log_le_self 2 (by omega))
    have heven : Even ((2 : ℕ) ^ k) := Even.pow_of_ne_zero even_two (by omega)
    have hm : n - 2 ^ k ∈ exceptions := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, hzero⟩
      exact (Nat.even_sub (by omega)).mpr ⟨fun _ => heven, fun _ => hnEven⟩
    exact Finset.mem_image.mpr ⟨(k, n - 2 ^ k), Finset.mem_product.mpr ⟨hkI, hm⟩,
      Nat.sub_add_cancel (by omega)⟩
  calc
    bad.card ≤ (pairs.image target).card := Finset.card_le_card cover
    _ ≤ pairs.card := Finset.card_image_le
    _ = K * exceptions.card := by simp [pairs, exponents, Finset.card_product, Nat.card_Icc]
