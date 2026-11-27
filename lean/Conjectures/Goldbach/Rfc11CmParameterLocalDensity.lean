import Mathlib

namespace GoldbachCmLocal

private def residues (r : ℕ) : Finset ℕ :=
  (Finset.range 105).filter fun t =>
    Nat.Coprime (t + 104) 105 ∧ Nat.Coprime ((r + 1 + 105 - t) % 105) 105

/- The two forbidden classes modulo each of 3, 5 and 7 leave at least
15 classes modulo 105. This finite check uses only the residue of the target. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem residue_count : ∀ r : Fin 105, 15 ≤ (residues r.val).card := by
  decide +kernel

theorem block_count (n s a : ℕ) :
    15 ≤ ((Finset.range 105).filter (fun i => let x := 2^s*(2*(a+i)+1);
      Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x%105))%105) 105)).card := by
  let x (i : ℕ) := 2^s * (2*(a+i)+1)
  let f (i : ℕ) := x i % 105
  let block := Finset.range 105
  have htwo : Nat.Coprime 2 105 := by decide
  have inj : Set.InjOn f (block : Set ℕ) := by
    intro i hi j hj hij
    have h : 2^s * (2*(a+i)+1) ≡ 2^s * (2*(a+j)+1) [MOD 105] := hij
    have h' := Nat.ModEq.cancel_left_of_coprime (htwo.pow_left s).symm.gcd_eq_one h
    have h'' := Nat.ModEq.cancel_left_of_coprime htwo.symm.gcd_eq_one
      (h'.add_right_cancel' 1)
    exact (h''.add_left_cancel' a).eq_of_lt_of_lt (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  have onto : block.image f = block := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (Nat.mod_lt _ (by decide))
    · exact (Finset.card_image_of_injOn inj).symm.le
  have good (i : ℕ) :
      (Nat.Coprime (x i + 104) 105 ∧ Nat.Coprime ((n+1+105-f i)%105) 105) ↔
      f i ∈ residues (n%105) := by
    have hlt : f i < 105 := Nat.mod_lt _ (by decide)
    have hc := ((Nat.mod_modEq (x i) 105).add_right 104).gcd_eq
    have hn : (n+1+105-f i)%105 = (n%105+1+105-f i)%105 := by
      rw [show n+1+105-f i = n+(106-f i) by omega,
        show n%105+1+105-f i = n%105+(106-f i) by omega]
      exact ((Nat.mod_modEq n 105).add_right _).symm
    change Nat.gcd (x i + 104) 105 = 1 ∧ _ ↔ _
    change Nat.gcd (f i + 104) 105 = Nat.gcd (x i + 104) 105 at hc
    simp only [residues, Finset.mem_filter, Finset.mem_range, hlt, true_and,
      Nat.Coprime, hn, hc]
  have hc :
      (block.filter (fun i => Nat.Coprime (x i+104) 105 ∧
        Nat.Coprime ((n+1+105-f i)%105) 105)).card = (residues (n%105)).card := by
    apply Finset.card_bij (fun i _ => f i)
    · exact fun i hi => (good i).mp (Finset.mem_filter.mp hi).2
    · exact fun i hi j hj hij => inj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
    · intro j hj
      have hmem : j ∈ block.image f := by
        rw [onto]
        exact (Finset.mem_filter.mp hj).1
      obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hmem
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, (good i).mpr (hfi.symm ▸ hj)⟩, hfi⟩
  exact (residue_count ⟨n%105, Nat.mod_lt _ (by decide)⟩).trans_eq hc.symm

end GoldbachCmLocal

theorem Conjectures.Goldbach.Rfc11CmParameterLocalDensity :
    ∀ n s a : ℕ, 2∣n → 1 ≤ s → 15 ≤ ((Finset.range 105).filter (fun i => let x := 2^s*(2*(a+i)+1); Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x%105))%105) 105)).card := by
  intro n s a _ _
  exact GoldbachCmLocal.block_count n s a
