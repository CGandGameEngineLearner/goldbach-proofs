import Mathlib

theorem PEqualNP.Outside.L_log_rank_six_point_equality :
    ∀ A : Finset (Fin 6), A.card = 3 → let L := (Finset.univ : Finset (Fin 6)).powersetCard 3; (L.filter (fun B => (A ∩ B).card ≠ 1 ∧ (A ∩ B).card ≠ 2)).card = 2 ∧ L.card = 20 := by
  decide
