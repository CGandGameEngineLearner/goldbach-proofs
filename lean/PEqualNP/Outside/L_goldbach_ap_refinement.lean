import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_refinement :
    let ap := fun (q a N : ℕ) (f : ℕ → ℝ) => Finset.sum ((Finset.range (N+1)).filter (fun k => k % q = a)) f;
    ∀ q d a N f, 0<q → 0<d → a<q → ap q a N f = Finset.sum (Finset.range d) (fun j => ap (q*d) (a+j*q) N f) := by
  dsimp only
  intro q d a N f hq hd ha
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hmain : ∀ m : ℕ, (q * m + a) % (q * d) = a + q * (m % d) := by
    intro m
    have hm : m = d * (m / d) + m % d := (Nat.div_add_mod m d).symm
    have hlt : a + q * (m % d) < q * d := by
      have hr : m % d < d := Nat.mod_lt _ hd
      calc
        a + q * (m % d) < q + q * (m % d) := Nat.add_lt_add_right ha _
        _ = q * ((m % d) + 1) := by ring
        _ ≤ q * d := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hr)
    calc
      (q * m + a) % (q * d) = (q * (d * (m / d) + m % d) + a) % (q * d) := by
        conv_lhs => rw [hm]
      _ = (a + q * (m % d) + (m / d) * (q * d)) % (q * d) := by
        congr 1
        ring
      _ = (a + q * (m % d)) % (q * d) := by
        rw [Nat.add_mul_mod_self_right]
      _ = a + q * (m % d) := Nat.mod_eq_of_lt hlt
  by_cases hka : k % q = a
  · let j0 := (k / q) % d
    have hj0 : j0 ∈ Finset.range d := Finset.mem_range.mpr (Nat.mod_lt _ hd)
    have hk0 : k % (q * d) = a + j0 * q := by
      have hkdec : k = q * (k / q) + a := by
        rw [← hka]
        exact (Nat.div_add_mod k q).symm
      conv_lhs => rw [hkdec]
      rw [hmain]
      dsimp [j0]
      rw [Nat.mul_comm]
    rw [Finset.sum_eq_single_of_mem j0 hj0]
    · simp [hka, hk0]
    · intro j hj hne
      have hneq : k % (q * d) ≠ a + j * q := by
        intro h
        apply hne
        have hsum : a + j0 * q = a + j * q := by rw [← hk0, h]
        have hmul : j0 * q = j * q := Nat.add_left_cancel hsum
        exact (Nat.mul_right_cancel hq hmul).symm
      simp [hneq]
  · have hfalse : ∀ j ∈ Finset.range d, k % (q * d) ≠ a + j * q := by
      intro j hj h
      apply hka
      have hmod : (a + j * q) % q = a := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
      calc
        k % q = k % (q * d) % q := by rw [Nat.mod_mul_right_mod]
        _ = (a + j * q) % q := by rw [h]
        _ = a := hmod
    rw [Finset.sum_eq_zero]
    · simp [hka]
    · intro j hj
      simp [hfalse j hj]
