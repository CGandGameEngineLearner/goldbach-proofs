import Mathlib

namespace PEqualNP.Outside

theorem L_log_rank_cert_8_7 :
    (∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 8; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 7; R.card*C.card=Nat.choose S.card 8*Nat.choose (n-S.card) 7 ∧ ∀ A∈R,∀ B∈C,Disjoint A B) := by
  intro n S R C
  refine ⟨?_, ?_⟩
  · have hR : R.card = Nat.choose S.card 8 := Finset.card_powersetCard 8 S
    have hC : C.card = Nat.choose ((Finset.univ : Finset (Fin n)) \ S).card 7 :=
      Finset.card_powersetCard 7 ((Finset.univ : Finset (Fin n)) \ S)
    have hdisj : Disjoint S ((Finset.univ : Finset (Fin n)) \ S) := by
      rw [Finset.disjoint_left]
      intro x hxS hxD
      exact (Finset.mem_sdiff.mp hxD).2 hxS
    have hunion : S ∪ ((Finset.univ : Finset (Fin n)) \ S) = Finset.univ := by
      ext x
      rw [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro _
        exact Finset.mem_univ x
      · intro hxu
        by_cases hx : x ∈ S
        · exact Or.inl hx
        · exact Or.inr ⟨hxu, hx⟩
    have hsum : S.card + ((Finset.univ : Finset (Fin n)) \ S).card = n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have hsdiff : ((Finset.univ : Finset (Fin n)) \ S).card = n - S.card := by omega
    rw [hR, hC, hsdiff]
  · intro A hA B hB
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    have hBC : B ⊆ (Finset.univ : Finset (Fin n)) \ S := (Finset.mem_powersetCard.mp hB).1
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp (hBC hxB)).2 (hAS hxA)

end PEqualNP.Outside
