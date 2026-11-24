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

private theorem aux_vecsq (q : ℕ) (s : Fin q → ℕ)
    (hsum : Finset.sum Finset.univ s = q ^ 2) :
    Finset.sum Finset.univ (fun y => s y * (s y - 1))
      = Finset.sum Finset.univ (fun y => s y ^ 2) - q ^ 2 := by
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
  rw [hterm, hsplit, hsum]

private theorem aux_cast_sum_sq (n : ℕ) (f : Fin n → ℕ) :
    Finset.sum Finset.univ (fun y : Fin n => (f y : ℤ) ^ 2)
      = ((Finset.sum Finset.univ (fun y : Fin n => f y ^ 2) : ℕ) : ℤ) := by
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun y _ => (Nat.cast_pow (f y) 2).symm)

private theorem aux_var (q : ℕ) (s : Fin q → ℕ)
    (hsum : Finset.sum Finset.univ s = q ^ 2)
    (hX3 : Finset.sum Finset.univ (fun y => s y ^ 2) = q ^ 3) :
    Finset.sum Finset.univ (fun y : Fin q => (((s y : ℤ) - (q : ℤ)) ^ 2)) = 0 := by
  have hterm : Finset.sum Finset.univ (fun y : Fin q => (((s y : ℤ) - (q : ℤ)) ^ 2))
      = Finset.sum Finset.univ (fun y : Fin q => ((s y : ℤ) ^ 2 - 2 * (q : ℤ) * (s y : ℤ) + (q : ℤ) ^ 2)) :=
    Finset.sum_congr rfl (fun y _ => by ring)
  rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hA : Finset.sum Finset.univ (fun y : Fin q => (s y : ℤ) ^ 2) = (q : ℤ) ^ 3 := by
    rw [aux_cast_sum_sq q s, hX3, Nat.cast_pow]
  have hB : Finset.sum Finset.univ (fun y : Fin q => 2 * (q : ℤ) * (s y : ℤ)) = 2 * (q : ℤ) * (q : ℤ) ^ 2 := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, hsum, Nat.cast_pow]
  have hC : Finset.sum Finset.univ (fun y : Fin q => (q : ℤ) ^ 2) = (q : ℤ) * (q : ℤ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
  rw [hA, hB, hC]
  ring

private theorem aux_fwd (q : ℕ) (s : Fin q → ℕ) (hq : 2 ≤ q)
    (hsum : Finset.sum Finset.univ s = q ^ 2)
    (hp : Finset.sum Finset.univ (fun y => s y * (s y - 1)) = q ^ 2 * (q - 1)) :
    ∀ y, s y = q := by
  have hq0 : 0 < q := by omega
  have hX2 := aux_vecsq q s hsum
  have hXge : q ^ 2 ≤ Finset.sum Finset.univ (fun y => s y ^ 2) := by
    rw [← hsum]
    exact Finset.sum_le_sum (fun y _ => aux_le_sq (s y))
  have hqq : q ^ 2 * (q - 1) + q ^ 2 = q ^ 3 := by
    have hstep : (q - 1) + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
    calc
      q ^ 2 * (q - 1) + q ^ 2 = q ^ 2 * ((q - 1) + 1) := by ring
      _ = q ^ 2 * q := by rw [hstep]
      _ = q ^ 3 := by ring
  have hX3 : Finset.sum Finset.univ (fun y => s y ^ 2) = q ^ 3 := by
    have h1 : Finset.sum Finset.univ (fun y => s y ^ 2)
        = (Finset.sum Finset.univ (fun y => s y ^ 2) - q ^ 2) + q ^ 2 :=
      (Nat.sub_add_cancel hXge).symm
    rw [h1, ← hX2, hp]
    exact hqq
  have hvar := aux_var q s hsum hX3
  have hzero : ∀ y ∈ (Finset.univ : Finset (Fin q)), (s y : ℤ) - (q : ℤ) = 0 :=
    (Finset.sum_sq_eq_zero_iff (s := (Finset.univ : Finset (Fin q)))
      (f := fun y : Fin q => ((s y : ℤ) - (q : ℤ)))).mp hvar
  intro y
  have h3 : (s y : ℤ) = (q : ℤ) := sub_eq_zero.mp (hzero y (Finset.mem_univ y))
  exact Nat.cast_injective h3

private theorem aux_bwd (q : ℕ) (s : Fin q → ℕ) (hall : ∀ y, s y = q) :
    Finset.sum Finset.univ (fun y => s y * (s y - 1)) = q ^ 2 * (q - 1) := by
  have h1 : ∀ y ∈ (Finset.univ : Finset (Fin q)), s y * (s y - 1) = q * (q - 1) := by
    intro y _
    rw [hall y]
  have h2 : Finset.sum Finset.univ (fun y => s y * (s y - 1))
      = Finset.sum Finset.univ (fun _ : Fin q => q * (q - 1)) :=
    Finset.sum_congr rfl h1
  rw [h2]
  rw [Finset.sum_const_nat (m := q * (q - 1)) (fun _ _ => rfl)]
  rw [Finset.card_univ, Fintype.card_fin]
  ring

theorem PEqualNP.Outside.L_hash_collision_lab_balanced_equality :
    ∀ (q : ℕ) (h : Fin (q^2) → Fin q), 2 ≤ q → let size := fun y : Fin q => (Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card; let pairs := ((Finset.univ : Finset (Fin (q^2) × Fin (q^2))).filter (fun z => z.1 ≠ z.2 ∧ h z.1 = h z.2)).card; (pairs = q^2*(q-1) ↔ ∀ y, size y = q) := by
  intro q h hq
  dsimp only
  have hid := aux_pairs (q ^ 2) q h
  have hsum := aux_sum (q ^ 2) q h
  constructor
  · intro hp
    have hstep : Finset.sum Finset.univ (fun y : Fin q => (Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card * ((Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card - 1)) = q^2*(q-1) := by
      rw [← hid]
      exact hp
    exact aux_fwd q (fun y : Fin q => (Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card) hq hsum hstep
  · intro hy
    rw [hid]
    exact aux_bwd q (fun y : Fin q => (Finset.univ.filter (fun x : Fin (q^2) => h x = y)).card) hy
