import Mathlib

theorem Conjectures.Cuts.Taske288f69a0908d43f9d978ed2 : (∀ (x1 : Finset ℕ) (x2 x3 : ℕ → ℕ),   have x4 : ℕ → ℕ → ℕ := fun (x4 x5 : ℕ) => ∑ x6 ∈ x1, (x2 x6).choose x4 * (x3 x6).choose x5;   ∑ x5 ∈ x1, (x2 x5 * x3 x5) ^ (2 : ℕ) = x4 (1 : ℕ) (1 : ℕ) + (2 : ℕ) * x4 (2 : ℕ) (1 : ℕ) + (2 : ℕ) * x4 (1 : ℕ) (2 : ℕ) + (4 : ℕ) * x4 (2 : ℕ) (2 : ℕ)) := by
  intro x1 x2 x3 x4
  -- `2 * choose a 2 = a * (a - 1)` for every natural number `a`.
  have h2 : ∀ a : ℕ, 2 * a.choose 2 = a * (a - 1) := by
    intro a
    rw [Nat.choose_two_right]
    obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd a
    · exact Nat.mul_div_cancel' (dvd_mul_of_dvd_left (show (2 : ℕ) ∣ k + k by omega) (k + k - 1))
    · rw [Nat.add_sub_cancel]
      exact Nat.mul_div_cancel' (dvd_mul_of_dvd_right (show (2 : ℕ) ∣ 2 * k by omega) (2 * k + 1))
  -- The pointwise identity: for `a = x2 m`, `b = x3 m`,
  -- `(a * b)^2 = ab + 2 C(a,2) b + 2 a C(b,2) + 4 C(a,2) C(b,2)`.
  have key : ∀ m : ℕ, (x2 m * x3 m) ^ 2 =
      x2 m * x3 m + 2 * ((x2 m).choose 2 * x3 m) + 2 * (x2 m * (x3 m).choose 2) +
        4 * ((x2 m).choose 2 * (x3 m).choose 2) := by
    intro m
    rcases Nat.eq_zero_or_pos (x2 m) with h0 | ha
    · simp [h0]
    rcases Nat.eq_zero_or_pos (x3 m) with h0 | hb
    · simp [h0]
    obtain ⟨a, ha'⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    obtain ⟨b, hb'⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    rw [Nat.succ_eq_add_one] at ha' hb'
    rw [ha', hb']
    have h1 := h2 (a + 1)
    have h1' := h2 (b + 1)
    simp only [Nat.add_sub_cancel] at h1 h1'
    have e1 : 2 * ((a + 1).choose 2 * (b + 1)) = (a + 1) * a * (b + 1) := by
      rw [show 2 * ((a + 1).choose 2 * (b + 1)) = 2 * (a + 1).choose 2 * (b + 1) by ring, h1]
    have e2 : 2 * ((a + 1) * (b + 1).choose 2) = (a + 1) * ((b + 1) * b) := by
      rw [show 2 * ((a + 1) * (b + 1).choose 2) = (a + 1) * (2 * (b + 1).choose 2) by ring, h1']
    have e3 : 4 * ((a + 1).choose 2 * (b + 1).choose 2) =
        ((a + 1) * a) * ((b + 1) * b) := by
      nlinarith [h1, h1']
    rw [e1, e2, e3]
    ring
  -- Sum the pointwise identity over the finite set.
  simp_rw [key, Finset.sum_add_distrib]
  simp only [x4, Nat.choose_one_right, ← Finset.mul_sum]
