import Mathlib

private lemma sq_sum_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hcirc : a ^ 2 + b ^ 2 = 1) :
    a + b ≤ 3 / 2 := by
  have hsq : (a + b) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  nlinarith

private lemma rot_ge (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hcirc : a ^ 2 + b ^ 2 = 1) :
    169 / 10 ≤ 17 * a + 7 * b := by
  have ha : 0 ≤ a := hb.trans hba
  have hdiff : (17 * a + 7 * b) ^ 2 - 288 * (a ^ 2 + b ^ 2) = (a - b) * (a + 239 * b) := by
    ring
  have hnonneg : 0 ≤ (a - b) * (a + 239 * b) :=
    mul_nonneg (sub_nonneg.mpr hba) (by linarith)
  rw [hcirc, mul_one] at hdiff
  have hsq : (169 / 10 : ℝ) ^ 2 ≤ (17 * a + 7 * b) ^ 2 := by
    linarith [show (169 / 10 : ℝ) ^ 2 ≤ 288 by norm_num]
  nlinarith

private lemma abs_lin_comb_le (c1 c2 d1 d2 M : ℝ)
    (hd1 : |d1| ≤ 1 / 40) (hd2 : |d2| ≤ 1 / 40) (hM : |c1| + |c2| ≤ M) :
    |c1 * d1 + c2 * d2| ≤ M / 40 := by
  calc
    |c1 * d1 + c2 * d2| ≤ |c1 * d1| + |c2 * d2| := abs_add_le _ _
    _ = |c1| * |d1| + |c2| * |d2| := by rw [abs_mul, abs_mul]
    _ ≤ |c1| * (1 / 40) + |c2| * (1 / 40) := by gcongr
    _ = (|c1| + |c2|) / 40 := by ring
    _ ≤ M / 40 := by gcongr

private lemma box_coord_lt (val err st : ℝ)
    (hid : val = st + err) (hst : |st| = 44 / 100) (herr : |err| ≤ 3 / 80) :
    |val| < 1 / 2 := by
  calc
    |val| = |st + err| := by rw [hid]
    _ ≤ |st| + |err| := abs_add_le _ _
    _ ≤ 44 / 100 + 3 / 80 := by rw [hst]; gcongr
    _ < 1 / 2 := by norm_num

private def gridX (j : Fin 10000) : ℚ := ((j.val / 100 : ℕ) : ℚ) / 20

private def gridY (j : Fin 10000) : ℚ := ((j.val % 100 : ℕ) : ℚ) / 20

private def gridW (j : Fin 10000) : ℕ :=
  if (130 : ℤ) ≤ |12 * ((j.val / 100 : ℕ) : ℤ) - 480 - 5 * ((j.val % 100 : ℕ) : ℤ) + 200|
  then 1 else 0

private lemma scaled_u_eq (i m : ℕ) :
    ((12 * (i : ℤ) - 480 - 5 * (m : ℤ) + 200 : ℤ) : ℝ) =
      260 * ((12 / 13 : ℝ) * ((((i : ℚ) / 20 : ℚ) : ℝ) - 2) +
             (-5 / 13 : ℝ) * ((((m : ℚ) / 20 : ℚ) : ℝ) - 2)) := by
  push_cast
  ring

private lemma grid_scaled_u_eq (j : Fin 10000) :
    ((12 * ((j.val / 100 : ℕ) : ℤ) - 480 - 5 * ((j.val % 100 : ℕ) : ℤ) + 200 : ℤ) : ℝ) =
      260 * ((12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2)) := by
  unfold gridX gridY
  exact scaled_u_eq (j.val / 100) (j.val % 100)

private lemma gridW_eq_one (j : Fin 10000)
    (hcond : (130 : ℤ) ≤ |12 * ((j.val / 100 : ℕ) : ℤ) - 480 - 5 * ((j.val % 100 : ℕ) : ℤ) + 200|) :
    gridW j = 1 := by
  unfold gridW
  split_ifs
  rfl

private lemma gridW_eq_zero (j : Fin 10000)
    (hcond : |12 * ((j.val / 100 : ℕ) : ℤ) - 480 - 5 * ((j.val % 100 : ℕ) : ℤ) + 200| < 130) :
    gridW j = 0 := by
  unfold gridW
  split_ifs <;> first | rfl | omega

private lemma single_le_univ_sum (f : Fin 10000 → ℕ) (j : Fin 10000) (h : 1 ≤ f j) :
    1 ≤ ∑ k : Fin 10000, f k :=
  h.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))

theorem Conjectures.SquarePacking.SeventeenChargeAngleRefutation :
    ¬ (let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; ∀ (k q : ℕ) (X Y : Fin k → ℚ) (w : Fin k → ℕ), (∀ x y a b : ℝ, 0 ≤ b → b ≤ a → (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2*x ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-x) ∧ |a| + |b| ≤ 2*y ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-y)) → q ≤ (∑ j : Fin k, (if inside x y a b (X j) (Y j) then w j else 0))) → ∀ x y a b : ℝ, (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2*x ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-x) ∧ |a| + |b| ≤ 2*y ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-y)) → q ≤ (∑ j : Fin k, (if inside x y a b (X j) (Y j) then w j else 0))) := by
  classical
  dsimp only
  intro hmain
  have hcov : ∀ x y a b : ℝ, 0 ≤ b → b ≤ a →
      (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2 * x ∧ |a| + |b| ≤ 2 * ((4661 / 1000 : ℝ) - x) ∧
        |a| + |b| ≤ 2 * y ∧ |a| + |b| ≤ 2 * ((4661 / 1000 : ℝ) - y)) →
      1 ≤ ∑ j : Fin 10000,
        (if |a * ((gridX j : ℝ) - x) + b * ((gridY j : ℝ) - y)| < 1 / 2 ∧
            |(-b) * ((gridX j : ℝ) - x) + a * ((gridY j : ℝ) - y)| < 1 / 2 then gridW j else 0) := by
    intro x y a b hb hba ⟨hcirc, hx1, hx2, hy1, hy2⟩
    have ha : 0 ≤ a := hb.trans hba
    have habs_a : |a| = a := abs_of_nonneg ha
    have habs_b : |b| = b := abs_of_nonneg hb
    rw [habs_a, habs_b] at hx1 hx2 hy1 hy2
    have hab_le : a + b ≤ 3 / 2 := sq_sum_le a b ha hb hcirc
    let u0 : ℝ := (12 / 13 : ℝ) * (x - 2) + (-5 / 13 : ℝ) * (y - 2)
    let s : ℝ := if 0 ≤ u0 then 1 else -1
    let px : ℝ := x + s * (44 / 100 : ℝ) * (a + b)
    let py : ℝ := y + s * (44 / 100 : ℝ) * (b - a)
    have hs_abs : s = 1 ∨ s = -1 := by dsimp [s]; split_ifs <;> simp
    have hpx_ge : 0 ≤ px := by
      rcases hs_abs with hs | hs <;> dsimp [px] <;> rw [hs] <;> linarith only [ha, hb, hx1]
    have hpx_le : px ≤ 4661 / 1000 := by
      rcases hs_abs with hs | hs <;> dsimp [px] <;> rw [hs] <;> linarith only [ha, hb, hx2]
    have hpy_ge : 0 ≤ py := by
      rcases hs_abs with hs | hs <;> dsimp [py] <;> rw [hs] <;> linarith only [ha, hb, hba, hy1]
    have hpy_le : py ≤ 4661 / 1000 := by
      rcases hs_abs with hs | hs <;> dsimp [py] <;> rw [hs] <;> linarith only [ha, hb, hba, hy2]
    let i : ℕ := Nat.floor (20 * px + 1 / 2)
    let m : ℕ := Nat.floor (20 * py + 1 / 2)
    have hi_lt : i < 100 := (Nat.floor_lt (by linarith only [hpx_ge])).mpr (by linarith only [hpx_le])
    have hm_lt : m < 100 := (Nat.floor_lt (by linarith only [hpy_ge])).mpr (by linarith only [hpy_le])
    have hi_le : (i : ℝ) ≤ 20 * px + 1 / 2 := Nat.floor_le (by linarith only [hpx_ge])
    have hi_gt : 20 * px + 1 / 2 < (i : ℝ) + 1 := Nat.lt_floor_add_one (20 * px + 1 / 2)
    have hm_le : (m : ℝ) ≤ 20 * py + 1 / 2 := Nat.floor_le (by linarith only [hpy_ge])
    have hm_gt : 20 * py + 1 / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one (20 * py + 1 / 2)
    let j : Fin 10000 := ⟨100 * i + m, by omega⟩
    have hj_div : j.val / 100 = i := by dsimp [j]; omega
    have hj_mod : j.val % 100 = m := by dsimp [j]; omega
    have hXj : (gridX j : ℝ) = (i : ℝ) / 20 := by unfold gridX; rw [hj_div]; push_cast; rfl
    have hYj : (gridY j : ℝ) = (m : ℝ) / 20 := by unfold gridY; rw [hj_mod]; push_cast; rfl
    have hdx_abs : |(gridX j : ℝ) - px| ≤ 1 / 40 := by
      rw [hXj]
      exact abs_le.mpr ⟨by linarith only [hi_gt], by linarith only [hi_le]⟩
    have hdy_abs : |(gridY j : ℝ) - py| ≤ 1 / 40 := by
      rw [hYj]
      exact abs_le.mpr ⟨by linarith only [hm_gt], by linarith only [hm_le]⟩
    have hst : |s * (44 / 100 : ℝ)| = 44 / 100 := by
      rcases hs_abs with hs | hs <;> rw [hs] <;> norm_num
    have hcoord1 : |a * ((gridX j : ℝ) - x) + b * ((gridY j : ℝ) - y)| < 1 / 2 := by
      have hid : a * ((gridX j : ℝ) - x) + b * ((gridY j : ℝ) - y) =
          s * (44 / 100 : ℝ) + (a * ((gridX j : ℝ) - px) + b * ((gridY j : ℝ) - py)) := by
        dsimp [px, py]
        calc
          a * ((gridX j : ℝ) - x) + b * ((gridY j : ℝ) - y)
            = s * (44 / 100 : ℝ) * (a ^ 2 + b ^ 2) +
                (a * ((gridX j : ℝ) - (x + s * (44 / 100 : ℝ) * (a + b))) +
                 b * ((gridY j : ℝ) - (y + s * (44 / 100 : ℝ) * (b - a)))) := by ring
          _ = s * (44 / 100 : ℝ) +
                (a * ((gridX j : ℝ) - (x + s * (44 / 100 : ℝ) * (a + b))) +
                 b * ((gridY j : ℝ) - (y + s * (44 / 100 : ℝ) * (b - a)))) := by rw [hcirc, mul_one]
      have herr : |a * ((gridX j : ℝ) - px) + b * ((gridY j : ℝ) - py)| ≤ 3 / 80 := by
        simpa [show (3 / 2 : ℝ) / 40 = 3 / 80 by norm_num] using
          abs_lin_comb_le a b ((gridX j : ℝ) - px) ((gridY j : ℝ) - py) (3 / 2) hdx_abs hdy_abs
            (by rw [habs_a, habs_b]; exact hab_le)
      exact box_coord_lt _ _ _ hid hst herr
    have hcoord2 : |(-b) * ((gridX j : ℝ) - x) + a * ((gridY j : ℝ) - y)| < 1 / 2 := by
      have hid : (-b) * ((gridX j : ℝ) - x) + a * ((gridY j : ℝ) - y) =
          -(s * (44 / 100 : ℝ)) + ((-b) * ((gridX j : ℝ) - px) + a * ((gridY j : ℝ) - py)) := by
        dsimp [px, py]
        calc
          (-b) * ((gridX j : ℝ) - x) + a * ((gridY j : ℝ) - y)
            = -(s * (44 / 100 : ℝ) * (a ^ 2 + b ^ 2)) +
                ((-b) * ((gridX j : ℝ) - (x + s * (44 / 100 : ℝ) * (a + b))) +
                 a * ((gridY j : ℝ) - (y + s * (44 / 100 : ℝ) * (b - a)))) := by ring
          _ = -(s * (44 / 100 : ℝ)) +
                ((-b) * ((gridX j : ℝ) - (x + s * (44 / 100 : ℝ) * (a + b))) +
                 a * ((gridY j : ℝ) - (y + s * (44 / 100 : ℝ) * (b - a)))) := by rw [hcirc, mul_one]
      have herr : |(-b) * ((gridX j : ℝ) - px) + a * ((gridY j : ℝ) - py)| ≤ 3 / 80 := by
        simpa [show (3 / 2 : ℝ) / 40 = 3 / 80 by norm_num] using
          abs_lin_comb_le (-b) a ((gridX j : ℝ) - px) ((gridY j : ℝ) - py) (3 / 2) hdx_abs hdy_abs
            (by rw [abs_neg, habs_a, habs_b]; linarith only [hab_le])
      exact box_coord_lt _ _ _ hid (by rw [abs_neg]; exact hst) herr
    have hrot : 169 / 10 ≤ 17 * a + 7 * b := rot_ge a b hb hba hcirc
    have hu_j : 1 / 2 < |(12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2)| := by
      have hid : (12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2) =
          u0 + s * (44 / 100 : ℝ) * ((17 * a + 7 * b) / 13) +
            ((12 / 13 : ℝ) * ((gridX j : ℝ) - px) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - py)) := by
        dsimp [u0, px, py]
        ring
      have herr : |(12 / 13 : ℝ) * ((gridX j : ℝ) - px) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - py)| ≤ 17 / 520 := by
        simpa [show (17 / 13 : ℝ) / 40 = 17 / 520 by norm_num] using
          abs_lin_comb_le (12 / 13) (-5 / 13) ((gridX j : ℝ) - px) ((gridY j : ℝ) - py) (17 / 13)
            hdx_abs hdy_abs (by norm_num)
      have herr_bounds := abs_le.mp herr
      rw [hid]
      by_cases hu0 : 0 ≤ u0
      · have hs1 : s = 1 := by dsimp [s]; split_ifs; rfl
        rw [hs1]
        have hge : 1 / 2 < u0 + 1 * (44 / 100 : ℝ) * ((17 * a + 7 * b) / 13) +
            ((12 / 13 : ℝ) * ((gridX j : ℝ) - px) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - py)) := by
          linarith only [hu0, hrot, herr_bounds.1]
        exact lt_of_lt_of_le hge (le_abs_self _)
      · have hs1 : s = -1 := by dsimp [s]; split_ifs; rfl
        rw [hs1]
        have hu0_neg : u0 < 0 := lt_of_not_ge hu0
        have hle : u0 + (-1) * (44 / 100 : ℝ) * ((17 * a + 7 * b) / 13) +
            ((12 / 13 : ℝ) * ((gridX j : ℝ) - px) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - py)) < -(1 / 2) := by
          linarith only [hu0_neg, hrot, herr_bounds.2]
        have hneg : 1 / 2 < -(u0 + (-1) * (44 / 100 : ℝ) * ((17 * a + 7 * b) / 13) +
            ((12 / 13 : ℝ) * ((gridX j : ℝ) - px) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - py))) := by
          linarith only [hle]
        exact lt_of_lt_of_le hneg (neg_le_abs _)
    have hwj : gridW j = 1 := by
      have hid_z := grid_scaled_u_eq j
      have h260 : |260 * ((12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2))| =
          260 * |(12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2)| := by
        rw [abs_mul, abs_of_nonneg (by norm_num)]
      have hgt : (130 : ℝ) <
          |((12 * ((j.val / 100 : ℕ) : ℤ) - 480 - 5 * ((j.val % 100 : ℕ) : ℤ) + 200 : ℤ) : ℝ)| := by
        rw [hid_z, h260]
        linarith only [hu_j]
      have habs_z : (130 : ℤ) < |12 * ((j.val / 100 : ℕ) : ℤ) - 480 - 5 * ((j.val % 100 : ℕ) : ℤ) + 200| := by
        exact_mod_cast hgt
      exact gridW_eq_one j (by omega)
    have hterm : 1 ≤ if |a * ((gridX j : ℝ) - x) + b * ((gridY j : ℝ) - y)| < 1 / 2 ∧
        |(-b) * ((gridX j : ℝ) - x) + a * ((gridY j : ℝ) - y)| < 1 / 2 then gridW j else 0 := by
      split_ifs with hcond
      · rw [hwj]
      · exact absurd ⟨hcoord1, hcoord2⟩ hcond
    exact single_le_univ_sum (fun k =>
      if |a * ((gridX k : ℝ) - x) + b * ((gridY k : ℝ) - y)| < 1 / 2 ∧
          |(-b) * ((gridX k : ℝ) - x) + a * ((gridY k : ℝ) - y)| < 1 / 2 then gridW k else 0)
      j hterm
  have hbad := hmain 10000 1 gridX gridY gridW hcov 2 2 (12 / 13 : ℝ) (-5 / 13 : ℝ) (by norm_num)
  have hzero : ∀ j : Fin 10000,
      (if |(12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2)| < 1 / 2 ∧
          |(-(-5 / 13 : ℝ)) * ((gridX j : ℝ) - 2) + (12 / 13 : ℝ) * ((gridY j : ℝ) - 2)| < 1 / 2
        then gridW j else 0) = 0 := by
    intro j
    split_ifs with hcond
    · have hid_z := grid_scaled_u_eq j
      have h260 : |260 * ((12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2))| =
          260 * |(12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2)| := by
        rw [abs_mul, abs_of_nonneg (by norm_num)]
      have hlt_r :
          |((12 * ((j.val / 100 : ℕ) : ℤ) - 480 - 5 * ((j.val % 100 : ℕ) : ℤ) + 200 : ℤ) : ℝ)| <
          (130 : ℝ) := by
        rw [hid_z, h260]
        linarith only [hcond.1]
      have hlt_z : |12 * ((j.val / 100 : ℕ) : ℤ) - 480 - 5 * ((j.val % 100 : ℕ) : ℤ) + 200| < 130 := by
        exact_mod_cast hlt_r
      exact gridW_eq_zero j hlt_z
    · rfl
  have hsum_zero :
      (∑ j : Fin 10000,
        (if |(12 / 13 : ℝ) * ((gridX j : ℝ) - 2) + (-5 / 13 : ℝ) * ((gridY j : ℝ) - 2)| < 1 / 2 ∧
            |(-(-5 / 13 : ℝ)) * ((gridX j : ℝ) - 2) + (12 / 13 : ℝ) * ((gridY j : ℝ) - 2)| < 1 / 2
          then gridW j else 0)) = 0 :=
    Finset.sum_eq_zero fun j _ => hzero j
  rw [hsum_zero] at hbad
  omega
