import Mathlib

private theorem aux_pairs (n m : ℕ) (h : Fin n → Fin m) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2 ∧ h z.1 = h z.2)).card
      = Finset.sum Finset.univ (fun y : Fin m => (Finset.univ.filter (fun x : Fin n => h x = y)).card * ((Finset.univ.filter (fun x : Fin n => h x = y)).card - 1)) := by
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2 ∧ h z.1 = h z.2))
    (t := (Finset.univ : Finset (Fin m)))
    (f := fun z : Fin n × Fin n => h z.1)
    (fun z _ => Finset.mem_univ _)
  rw [hfib]
  apply Finset.sum_congr rfl
  intro y _
  have hoff : (((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2 ∧ h z.1 = h z.2)).filter (fun z => h z.1 = y)).card
      = (Finset.univ.filter (fun x : Fin n => h x = y)).card * ((Finset.univ.filter (fun x : Fin n => h x = y)).card - 1) := by
    have hset : (((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2 ∧ h z.1 = h z.2)).filter (fun z => h z.1 = y))
        = (Finset.univ.filter (fun x : Fin n => h x = y)).offDiag := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
      constructor
      · rintro ⟨⟨hne, heq⟩, hy⟩
        exact ⟨hy, by rw [← heq, hy], hne⟩
      · rintro ⟨h1, h2, hne⟩
        exact ⟨⟨hne, by rw [h1, h2]⟩, h1⟩
    rw [hset, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
  exact hoff

theorem PEqualNP.Outside.L_hash_collision_lab_ordered_pair_identity :
    ∀ (n m : ℕ) (h : Fin n → Fin m), let size := fun y : Fin m => (Finset.univ.filter (fun x : Fin n => h x = y)).card; let pairs := ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2 ∧ h z.1 = h z.2)).card; pairs = Finset.sum Finset.univ (fun y => size y * (size y - 1)) := by
  intro n m h
  dsimp only
  exact aux_pairs n m h
