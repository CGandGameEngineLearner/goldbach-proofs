import Mathlib

private lemma proj_bound (x y a b u v X Y : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (huv : u ≠ 0 ∨ v ≠ 0)
    (h1 : |a * (X - x) + b * (Y - y)| < 1 / 2)
    (h2 : |(-b) * (X - x) + a * (Y - y)| < 1 / 2) :
    |u * (X - x) + v * (Y - y)| < (|u * a + v * b| + |v * a - u * b|) / 2 := by
  set p := a * (X - x) + b * (Y - y) with hp
  set q := (-b) * (X - x) + a * (Y - y) with hq
  have hdx : X - x = a * p - b * q := by
    have h : a * p - b * q = (a ^ 2 + b ^ 2) * (X - x) := by
      rw [hp, hq]; ring
    rw [h, hab]; ring
  have hdy : Y - y = b * p + a * q := by
    have h : b * p + a * q = (a ^ 2 + b ^ 2) * (Y - y) := by
      rw [hp, hq]; ring
    rw [h, hab]; ring
  have hkey : u * (X - x) + v * (Y - y) = p * (u * a + v * b) + q * (v * a - u * b) := by
    rw [hdx, hdy]; ring
  rw [hkey]
  set c1 := u * a + v * b with hc1
  set c2 := v * a - u * b with hc2
  have hcu : u = a * c1 - b * c2 := by
    have h : a * c1 - b * c2 = (a ^ 2 + b ^ 2) * u := by rw [hc1, hc2]; ring
    rw [h, hab]; ring
  have hcv : v = b * c1 + a * c2 := by
    have h : b * c1 + a * c2 = (a ^ 2 + b ^ 2) * v := by rw [hc1, hc2]; ring
    rw [h, hab]; ring
  have hcpos : 0 < |c1| + |c2| := by
    by_cases h1c : |c1| = 0
    · have e1 : c1 = 0 := abs_eq_zero.mp h1c
      have h2c : |c2| ≠ 0 := by
        intro h2c
        have e2 : c2 = 0 := abs_eq_zero.mp h2c
        rcases huv with hu | hv
        · apply hu
          rw [e1, e2] at hcu
          simpa using hcu
        · apply hv
          rw [e1, e2] at hcv
          simpa using hcv
      have : 0 < |c2| := lt_of_le_of_ne (abs_nonneg c2) (Ne.symm h2c)
      linarith [abs_nonneg c1]
    · have : 0 < |c1| := lt_of_le_of_ne (abs_nonneg c1) (Ne.symm h1c)
      linarith [abs_nonneg c2]
  have hstep1 : |p * c1 + q * c2| ≤ |p| * |c1| + |q| * |c2| := by
    calc |p * c1 + q * c2| ≤ |p * c1| + |q * c2| := abs_add_le _ _
      _ = |p| * |c1| + |q| * |c2| := by rw [abs_mul, abs_mul]
  have hp' : |p| < 1 / 2 := by rw [hp]; exact h1
  have hq' : |q| < 1 / 2 := by rw [hq]; exact h2
  have hstep2 : |p * c1 + q * c2| ≤ max |p| |q| * (|c1| + |c2|) := by
    refine hstep1.trans ?_
    have hA : |p| * |c1| ≤ max |p| |q| * |c1| :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg c1)
    have hB : |q| * |c2| ≤ max |p| |q| * |c2| :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg c2)
    nlinarith [hA, hB]
  have hstep3 : max |p| |q| * (|c1| + |c2|) < (1 / 2) * (|c1| + |c2|) :=
    mul_lt_mul_of_pos_right (max_lt hp' hq') hcpos
  calc |p * c1 + q * c2| ≤ max |p| |q| * (|c1| + |c2|) := hstep2
    _ < (1 / 2) * (|c1| + |c2|) := hstep3
    _ = (|c1| + |c2|) / 2 := by ring

private lemma disjoint_of_sep (x y a b z w c d u v : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) (hcd : c ^ 2 + d ^ 2 = 1)
    (huv : u ≠ 0 ∨ v ≠ 0)
    (hsep : (|u * a + v * b| + |v * a - u * b|) / 2 +
      (|u * c + v * d| + |v * c - u * d|) / 2 ≤ |u * (z - x) + v * (w - y)|) :
    ∀ X Y : ℝ,
      |a * (X - x) + b * (Y - y)| < 1 / 2 →
      |(-b) * (X - x) + a * (Y - y)| < 1 / 2 →
      ¬ (|c * (X - z) + d * (Y - w)| < 1 / 2 ∧
         |(-d) * (X - z) + c * (Y - w)| < 1 / 2) := by
  intro X Y h1 h2
  rintro ⟨h3, h4⟩
  have p1 := proj_bound x y a b u v X Y hab huv h1 h2
  have p2 := proj_bound z w c d u v X Y hcd huv h3 h4
  have htri : |u * (z - x) + v * (w - y)| ≤
      |u * (X - x) + v * (Y - y)| + |u * (X - z) + v * (Y - w)| := by
    have e : u * (z - x) + v * (w - y) =
        (u * (X - x) + v * (Y - y)) - (u * (X - z) + v * (Y - w)) := by ring
    rw [e]
    have h := abs_sub_le (u * (X - x) + v * (Y - y)) 0 (u * (X - z) + v * (Y - w))
    rw [sub_zero, zero_sub, abs_neg] at h
    exact h
  linarith

private noncomputable def PX : Fin 11 → ℝ :=
  ![(2503/5000), (16897/5000), (1584/625), (2503/5000), (2503/5000), (3753/2500), (3183/2500), (9689/5000), (1961/1000), (1641/625), (31747/10000)]

private noncomputable def PY : Fin 11 → ℝ :=
  ![(2503/5000), (2503/5000), (3379/1000), (16897/5000), (5947/2500), (16897/5000), (14537/10000), (1763/2500), (21901/10000), (901/625), (11711/5000)]

private noncomputable def PA : Fin 11 → ℝ :=
  ![1, 1, 1, 1, 1, 1, (728/953), (728/953), (728/953), (728/953), (728/953)]

private noncomputable def PB : Fin 11 → ℝ :=
  ![0, 0, 0, 0, 0, 0, (615/953), (615/953), (615/953), (615/953), (615/953)]

private noncomputable def PU : Fin 11 → Fin 11 → ℝ :=
  !![
     1, 728, 728, -615, -615, 728, 728, 728, 728, 728, 728;
     -728, 1, -615, -615, -615, -615, -615, 1, -615, -615, -615;
     -728, 615, 1, 728, 728, 1, 728, 728, 728, -615, -615;
     615, 615, -728, 1, 0, 1, -615, -615, -615, -615, -615;
     615, 615, -728, 0, 1, 728, -615, -615, 1, -615, 728;
     -728, 615, -1, -1, -728, 1, 728, -615, -615, -615, -615;
     -728, 615, -728, 615, 615, -728, 1, -615, 728, 728, 728;
     -728, -1, -728, 615, 615, 615, 615, 1, -615, 728, 728;
     -728, 615, -728, 615, -1, 615, -728, 615, 1, -615, 728;
     -728, 615, 615, 615, 615, 615, -728, -728, 615, 1, 728;
     -728, 615, 615, 615, -728, 615, -728, -728, -728, -728, 1]

private noncomputable def PV : Fin 11 → Fin 11 → ℝ :=
  !![
     0, 615, 615, 728, 728, 615, 615, 615, 615, 615, 615;
     -615, 0, 728, 728, 728, 728, 728, 0, 728, 728, 728;
     -615, -728, 0, 615, 615, 0, 615, 615, 615, 728, 728;
     -728, -728, -615, 0, 1, 0, 728, 728, 728, 728, 728;
     -728, -728, -615, -1, 0, 615, 728, 728, 0, 728, 615;
     -615, -728, 0, 0, -615, 0, 615, 728, 728, 728, 728;
     -615, -728, -615, -728, -728, -615, 0, 728, 615, 615, 615;
     -615, 0, -615, -728, -728, -728, -728, 0, 728, 615, 615;
     -615, -728, -615, -728, 0, -728, -615, -728, 0, 728, 615;
     -615, -728, -728, -728, -728, -728, -615, -615, -728, 0, 615;
     -615, -728, -728, -728, -615, -728, -615, -615, -615, -615, 0]

private lemma h_unit : ∀ i : Fin 11, PA i ^ 2 + PB i ^ 2 = 1 := by
  intro i
  fin_cases i <;> norm_num [PA, PB]

private lemma h_dir : ∀ i j : Fin 11, i ≠ j → PU i j ≠ 0 ∨ PV i j ≠ 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | simp [PU, PV]

private lemma h_par : ∀ i j : Fin 11, i ≠ j →
    (|PU i j * PA i + PV i j * PB i| + |PV i j * PA i - PU i j * PB i|) / 2 +
    (|PU i j * PA j + PV i j * PB j| + |PV i j * PA j - PU i j * PB j|) / 2 ≤
    |PU i j * (PX j - PX i) + PV i j * (PY j - PY i)| := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | norm_num [PX, PY, PA, PB, PU, PV]

theorem PEqualNP.Outside.L_square_packing_eleven_construction :
    let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; let fits := fun (n : ℕ) (s : ℝ) => 0 ≤ s ∧ ∃ x y a b : Fin n → ℝ, (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2*x i ∧ |a i| + |b i| ≤ 2*(s-x i) ∧ |a i| + |b i| ≤ 2*y i ∧ |a i| + |b i| ≤ 2*(s-y i)) ∧ (∀ i j, i ≠ j → ∀ X Y : ℝ, inside (x i) (y i) (a i) (b i) X Y → ¬ inside (x j) (y j) (a j) (b j) X Y); fits 11 (97/25) := by
  dsimp only
  refine ⟨by norm_num, PX, PY, PA, PB, ?_, ?_⟩
  · intro i
    fin_cases i <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [PX, PY, PA, PB]
  · intro i j hij X Y h1
    exact disjoint_of_sep (PX i) (PY i) (PA i) (PB i) (PX j) (PY j) (PA j) (PB j)
      (PU i j) (PV i j) (h_unit i) (h_unit j) (h_dir i j hij) (h_par i j hij) X Y h1.1 h1.2
