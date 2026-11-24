import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_bucket_partition :
    ∀ (n m : ℕ) (h : Fin n → Fin m), let size := fun y : Fin m => (Finset.univ.filter (fun x : Fin n => h x = y)).card; Finset.sum Finset.univ size = n := by
  intro n m h
  dsimp only
  have h1 := Finset.card_eq_sum_card_fiberwise (f := h)
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin m)))
    (fun x _ => Finset.mem_univ (h x))
  simpa using h1.symm
