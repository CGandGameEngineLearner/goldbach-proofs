import Mathlib

theorem Conjectures.Cuts.Taskc8efccc5def347d802d54f58 : (by
  classical
  exact ∀ (n d : ℕ) (U : Finset ℕ), 0<d → U ⊆ Finset.range (n+1) →
    (U.filter (fun p => d ∣ p+2)).card = ((Finset.range ((n+2)/d+1)).filter (fun k => 2≤d*k ∧ d*k-2 ∈ U)).card) := by
  classical
  intro n d U hd hU
  let V := (Finset.range ((n+2)/d+1)).filter (fun k=>2≤d*k ∧ d*k-2 ∈ U)
  have im : V.image (fun k=>d*k-2) = U.filter (fun p=>d∣p+2) := by
    ext p
    constructor
    · intro h
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨_,hlo,hu⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hu,⟨k,by omega⟩⟩
    · intro h
      obtain ⟨hp,div⟩ := Finset.mem_filter.mp h
      have eqp : d*((p+2)/d)=p+2 := Nat.mul_div_cancel' div
      have hpn := Finset.mem_range.mp (hU hp)
      have hbound : (p+2)/d ≤ (n+2)/d := Nat.div_le_div_right (by omega)
      have hin : d*((p+2)/d)-2=p := by omega
      exact Finset.mem_image.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,hin.symm ▸ hp⟩,hin⟩
  rw [← im]
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2.1
  have hj' := (Finset.mem_filter.mp hj).2.1
  dsimp at hij
  apply Nat.eq_of_mul_eq_mul_left hd
  omega
