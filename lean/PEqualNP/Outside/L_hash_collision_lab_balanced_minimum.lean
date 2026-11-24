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

private theorem aux_sum (n m : ℕ) (h : Fin n → Fin m) :
    Finset.sum Finset.univ (fun y : Fin m => (Finset.univ.filter (fun x : Fin n => h x = y)).card) = n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin m)))
    (f := h)
    (fun x _ => Finset.mem_univ _)
  simpa only [Finset.card_univ, Fintype.card_fin] using h.symm

private theorem aux_le_sq (c : ℕ) : c ≤ c ^ 2 := by
  simpa only [pow_two] using Nat.le_mul_self c

private theorem aux_min (q : ℕ) (s : Fin q → ℕ) (hq : 2 ≤ q)
    (hsum : Finset.sum Finset.univ s = q ^ 2) :
    q ^ 2 * (q - 1) ≤ Finset.sum Finset.univ (fun y => s y * (s y - 1)) := by
  have hq0 : 0 < q := by omega
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin q))) (f := s)
  rw [hsum] at hcs
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  have hpq : (q ^ 2) ^ 2 = q * q ^ 3 := by ring
  rw [hpq] at hcs
  have hX : q ^ 3 ≤ Finset.sum Finset.univ (fun y => s y ^ 2) :=
    Nat.le_of_mul_le_mul_left hcs hq0
  have hle : ∀ y ∈ (Finset.univ : Finset (Fin q)), s y ≤ s y ^ 2 := by
    intro y _
    exact aux_le_sq (s y)
  have hsplit : Finset.sum Finset.univ (fun y => s y ^ 2 - s y)
      = Finset.sum Finset.univ (fun y => s y ^ 2) - Finset.sum Finset.univ s :=
    Finset.sum_tsub_distrib (Finset.univ : Finset (Fin q)) hle
  have hterm : Finset.sum Finset.univ (fun y => s y * (s y - 1))
      = Finset.sum Finset.univ (fun y => s y ^ 2 - s y) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  have hpairs : Finset.sum Finset.univ (fun y => s y * (s y - 1))
      = Finset.sum Finset.univ (fun y => s y ^ 2) - q ^ 2 := by
    rw [hterm, hsplit, hsum]
  have hq3 : q ^ 3 = q ^ 2 * q := by ring
  calc
    q ^ 2 * (q - 1) = q ^ 3 - q ^ 2 := by
      rw [hq3, Nat.mul_sub_left_distrib, mul_one]
    _ ≤ Finset.sum Finset.univ (fun y => s y ^ 2) - q ^ 2 := Nat.sub_le_sub_right hX (q ^ 2)
    _ = Finset.sum Finset.univ (fun y => s y * (s y - 1)) := hpairs.symm

theorem PEqualNP.Outside.L_hash_collision_lab_balanced_minimum :
    ∀ (q : ℕ) (h : Fin (q^2) → Fin q), 2 ≤ q → let size := fun y : Fin q => (Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card; let pairs := ((Finset.univ : Finset (Fin (q^2) × Fin (q^2))).filter (fun z => z.1 ≠ z.2 ∧ h z.1 = h z.2)).card; q^2*(q-1) ≤ pairs := by
  intro q h hq
  dsimp only
  have hid := aux_pairs (q ^ 2) q h
  have hsum := aux_sum (q ^ 2) q h
  have hmin := aux_min q (fun y : Fin q => (Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card) hq hsum
  calc
    q^2*(q-1) ≤ Finset.sum Finset.univ (fun y : Fin q => (Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card * ((Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card - 1)) := hmin
    _ = ((Finset.univ : Finset (Fin (q^2) × Fin (q^2))).filter (fun z => z.1 ≠ z.2 ∧ h z.1 = h z.2)).card := hid.symm
