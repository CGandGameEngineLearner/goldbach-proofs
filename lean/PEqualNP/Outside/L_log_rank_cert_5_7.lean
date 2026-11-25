import Mathlib

/-- The 5-subsets of `S` and the 7-subsets of its complement form a disjoint rectangle. -/
theorem PEqualNP.Outside.L_log_rank_cert_5_7 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 5; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 7; R.card*C.card=Nat.choose S.card 5*Nat.choose (n-S.card) 7 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  constructor
  · simp only [Finset.card_powersetCard, Finset.card_univ_sdiff, Fintype.card_fin]
  · intro A hA B hB
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    have hBC : B ⊆ (Finset.univ : Finset (Fin n)) \ S := (Finset.mem_powersetCard.mp hB).1
    exact Finset.disjoint_left.mpr fun _ hxA hxB =>
      (Finset.mem_sdiff.mp (hBC hxB)).2 (hAS hxA)
