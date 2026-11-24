import Mathlib

private lemma proj_abs_comb (p q c d : ℝ) (hp : |p| < 1 / 2) (hq : |q| < 1 / 2)
    (hcd : c ≠ 0 ∨ d ≠ 0) : |c * p + d * q| < (|c| + |d|) / 2 := by
  have htri : |c * p + d * q| ≤ |c| * |p| + |d| * |q| := by
    calc
      |c * p + d * q| ≤ |c * p| + |d * q| := abs_add_le _ _
      _ = |c| * |p| + |d| * |q| := by rw [abs_mul, abs_mul]
  have hstep : |c| * |p| + |d| * |q| < (|c| + |d|) / 2 := by
    rcases hcd with hc | hd
    · have hcpos : 0 < |c| := abs_pos.mpr hc
      have h1 : |c| * |p| < |c| * (1 / 2) := mul_lt_mul_of_pos_left hp hcpos
      have h2 : |d| * |q| ≤ |d| * (1 / 2) := mul_le_mul_of_nonneg_left hq.le (abs_nonneg d)
      have h3 := add_lt_add_of_lt_of_le h1 h2
      have h4 : |c| * (1 / 2) + |d| * (1 / 2) = (|c| + |d|) / 2 := by ring
      linarith
    · have hdpos : 0 < |d| := abs_pos.mpr hd
      have h1 : |d| * |q| < |d| * (1 / 2) := mul_lt_mul_of_pos_left hq hdpos
      have h2 : |c| * |p| ≤ |c| * (1 / 2) := mul_le_mul_of_nonneg_left hp.le (abs_nonneg c)
      have h3 := add_lt_add_of_le_of_lt h2 h1
      have h4 : |c| * (1 / 2) + |d| * (1 / 2) = (|c| + |d|) / 2 := by ring
      linarith
  linarith

private lemma proj_key (a b u v : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (huv : u ≠ 0 ∨ v ≠ 0) :
    u * a + v * b ≠ 0 ∨ v * a - u * b ≠ 0 := by
  by_contra h
  have hc : u * a + v * b = 0 := by
    by_contra hc
    exact h (Or.inl hc)
  have hd : v * a - u * b = 0 := by
    by_contra hd
    exact h (Or.inr hd)
  have hu : u = a * (u * a + v * b) - b * (v * a - u * b) := by
    have e : a * (u * a + v * b) - b * (v * a - u * b) = (a ^ 2 + b ^ 2) * u := by ring
    rw [e, hab, one_mul]
  have hv : v = b * (u * a + v * b) + a * (v * a - u * b) := by
    have e : b * (u * a + v * b) + a * (v * a - u * b) = (a ^ 2 + b ^ 2) * v := by ring
    rw [e, hab, one_mul]
  rw [hc, hd] at hu hv
  simp only [mul_zero, sub_zero, add_zero] at hu hv
  rcases huv with h | h
  · exact h hu
  · exact h hv

private lemma proj_radius_aux (x y a b u v X Y : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (huv : u ≠ 0 ∨ v ≠ 0)
    (hX : |a * (X - x) + b * (Y - y)| < 1 / 2 ∧ |(-b) * (X - x) + a * (Y - y)| < 1 / 2) :
    |u * (X - x) + v * (Y - y)| < (|u * a + v * b| + |v * a - u * b|) / 2 := by
  have hcd := proj_key a b u v hab huv
  have hkey : u * (X - x) + v * (Y - y) =
      (u * a + v * b) * (a * (X - x) + b * (Y - y)) +
      (v * a - u * b) * ((-b) * (X - x) + a * (Y - y)) := by
    have e : u * (X - x) + v * (Y - y) =
        (a ^ 2 + b ^ 2) * (u * (X - x) + v * (Y - y)) := by
      rw [hab, one_mul]
    rw [e]
    ring
  calc
    |u * (X - x) + v * (Y - y)| = |(u * a + v * b) * (a * (X - x) + b * (Y - y)) +
        (v * a - u * b) * ((-b) * (X - x) + a * (Y - y))| := by rw [hkey]
    _ < (|u * a + v * b| + |v * a - u * b|) / 2 :=
        proj_abs_comb (a * (X - x) + b * (Y - y)) ((-b) * (X - x) + a * (Y - y))
          (u * a + v * b) (v * a - u * b) hX.1 hX.2 hcd

private lemma sep_aux :
    ∀ x y a b z w c d u v : ℝ, a ^ 2 + b ^ 2 = 1 → c ^ 2 + d ^ 2 = 1 →
      (u ≠ 0 ∨ v ≠ 0) →
      (|u * a + v * b| + |v * a - u * b|) / 2 +
          (|u * c + v * d| + |v * c - u * d|) / 2 ≤ |u * (z - x) + v * (w - y)| →
      ∀ X Y : ℝ,
        (|a * (X - x) + b * (Y - y)| < 1 / 2 ∧ |(-b) * (X - x) + a * (Y - y)| < 1 / 2) →
        ¬(|c * (X - z) + d * (Y - w)| < 1 / 2 ∧ |(-d) * (X - z) + c * (Y - w)| < 1 / 2) := by
  intro x y a b z w c d u v hab hcd huv hsep X Y hX hZ
  have h1 := proj_radius_aux x y a b u v X Y hab huv hX
  have h2 := proj_radius_aux z w c d u v X Y hcd huv hZ
  have h4 : |u * (z - x) + v * (w - y)| ≤
      |u * (X - x) + v * (Y - y)| + |u * (X - z) + v * (Y - w)| := by
    have e : u * (z - x) + v * (w - y) =
        (u * (X - x) + v * (Y - y)) - (u * (X - z) + v * (Y - w)) := by ring
    calc
      |u * (z - x) + v * (w - y)| =
          |(u * (X - x) + v * (Y - y)) - (u * (X - z) + v * (Y - w))| := by rw [e]
      _ = |(u * (X - x) + v * (Y - y)) + -(u * (X - z) + v * (Y - w))| := by
          rw [sub_eq_add_neg]
      _ ≤ |u * (X - x) + v * (Y - y)| + |u * (X - z) + v * (Y - w)| := by
          simpa only [abs_neg] using
            abs_add_le (u * (X - x) + v * (Y - y)) (-(u * (X - z) + v * (Y - w)))
  have h5 := add_lt_add h1 h2
  linarith

theorem PEqualNP.Outside.L_square_packing_separation_certificate :
    let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; let radius := fun (a b u v : ℝ) => (|u*a+v*b| + |v*a-u*b|)/2; ∀ x y a b z w c d u v : ℝ, a^2+b^2=1 → c^2+d^2=1 → (u ≠ 0 ∨ v ≠ 0) → radius a b u v + radius c d u v ≤ |u*(z-x)+v*(w-y)| → ∀ X Y : ℝ, inside x y a b X Y → ¬ inside z w c d X Y := by
  exact sep_aux
