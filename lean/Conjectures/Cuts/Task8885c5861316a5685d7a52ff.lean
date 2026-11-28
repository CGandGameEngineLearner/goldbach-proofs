import Mathlib

theorem Conjectures.Cuts.Task8885c5861316a5685d7a52ff :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
    ∀ X : ℕ, 16 ≤ X →
      let L := Nat.log 2 X / 2
      let E := (Finset.Ico X (2*X)).filter (fun n =>
        Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e) = 0)).card)
      E.card ≤ L * ((Finset.Icc 4 (2*X)).filter (fun m => Even m ∧ G m = 0)).card := by
  intro G X hX L E
  let exponents := Finset.Icc 1 L
  let exceptions := (Finset.Icc 4 (2*X)).filter (fun m => Even m ∧ G m = 0)
  let translate := fun p : ℕ × ℕ => p.2 + 2^p.1
  have cover : E ⊆ (exponents ×ˢ exceptions).image translate := by
    intro n hn
    obtain ⟨hnI, hnEven, hmiss⟩ := Finset.mem_filter.mp hn
    obtain ⟨hx, hupper⟩ := Finset.mem_Ico.mp hnI
    obtain ⟨e, he⟩ := Finset.card_pos.mp hmiss
    obtain ⟨heI, hzero⟩ := Finset.mem_filter.mp he
    obtain ⟨hepos, hemax⟩ := Finset.mem_Icc.mp heI
    have elog : e+1 ≤ Nat.log 2 X := by dsimp [L] at hemax; omega
    have hshift := (Nat.pow_le_pow_right (by decide : 0 < 2) elog).trans
      (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
    rw [pow_succ] at hshift
    have hpEven : Even (2^e : ℕ) := (show Even (2:ℕ) from ⟨1,rfl⟩).pow_of_ne_zero (by omega)
    have remEven : Even (n-2^e) := by
      rw [even_iff_two_dvd] at hnEven hpEven ⊢
      omega
    refine Finset.mem_image.mpr ⟨(e,n-2^e), Finset.mem_product.mpr ⟨heI, ?_⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, remEven, hzero⟩
    · dsimp [translate]
      omega
  calc
    _ ≤ ((exponents ×ˢ exceptions).image translate).card := Finset.card_le_card cover
    _ ≤ (exponents ×ˢ exceptions).card := Finset.card_image_le
    _ = L * exceptions.card := by simp [exponents, Nat.card_Icc]
