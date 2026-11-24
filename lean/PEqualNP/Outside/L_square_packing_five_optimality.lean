import Mathlib

noncomputable section

private def kk : ℝ := 2 + Real.sqrt 2 / 2

private noncomputable def pset : Finset (ℝ × ℝ) :=
  {(1, 1), (1, 1 + Real.sqrt 2 / 2), (1 + Real.sqrt 2 / 2, 1),
    (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2)}

private def csq (x y a b : ℝ) : Set (ℝ × ℝ) :=
  {p | |a * (p.1 - x) + b * (p.2 - y)| ≤ 1 / 2 ∧ |-b * (p.1 - x) + a * (p.2 - y)| ≤ 1 / 2}

private lemma w_ge_one (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : 1 ≤ |a| + |b| := by
  have hnn : 0 ≤ |a| + |b| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h2 : 1 ≤ (|a| + |b|) ^ 2 := by
    nlinarith [hab, abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]
  nlinarith

-- Lemma 1 in bbox form: center in [0,1]^2, square in first quadrant (bbox form)
private lemma corner_lemma (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hx0 : |a| + |b| ≤ 2 * x) (hy0 : |a| + |b| ≤ 2 * y)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    |a * (1 - x) + b * (1 - y)| ≤ 1 / 2 ∧ |-b * (1 - x) + a * (1 - y)| ≤ 1 / 2 := by
  have hw1 : 1 ≤ |a| + |b| := w_ge_one a b hab
  have hxw : (|a| + |b|) / 2 ≤ x := by linarith
  have hyw : (|a| + |b|) / 2 ≤ y := by linarith
  have ht1 : 0 ≤ 1 - x := by linarith
  have ht2 : 0 ≤ 1 - y := by linarith
  have hb1 : 1 - x ≤ 1 - (|a| + |b|) / 2 := by linarith
  have hb2 : 1 - y ≤ 1 - (|a| + |b|) / 2 := by linarith
  have hwle : (|a| + |b|) * (1 - (|a| + |b|) / 2) ≤ 1 / 2 := by
    nlinarith [sq_nonneg (|a| + |b| - 1), hw1]
  constructor
  · calc |a * (1 - x) + b * (1 - y)|
        ≤ |a| * (1 - x) + |b| * (1 - y) := by
          have h := abs_add_le (a * (1 - x)) (b * (1 - y))
          rw [abs_mul, abs_mul, abs_of_nonneg ht1, abs_of_nonneg ht2] at h
          exact h
      _ ≤ |a| * (1 - (|a| + |b|) / 2) + |b| * (1 - (|a| + |b|) / 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hb1 (abs_nonneg a))
            (mul_le_mul_of_nonneg_left hb2 (abs_nonneg b))
      _ = (|a| + |b|) * (1 - (|a| + |b|) / 2) := by ring
      _ ≤ 1 / 2 := hwle
  · calc |-b * (1 - x) + a * (1 - y)|
        ≤ |b| * (1 - x) + |a| * (1 - y) := by
          have h := abs_add_le ((-b) * (1 - x)) (a * (1 - y))
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg ht1, abs_of_nonneg ht2] at h
          exact h
      _ ≤ |b| * (1 - (|a| + |b|) / 2) + |a| * (1 - (|a| + |b|) / 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hb1 (abs_nonneg b))
            (mul_le_mul_of_nonneg_left hb2 (abs_nonneg a))
      _ = (|a| + |b|) * (1 - (|a| + |b|) / 2) := by ring
      _ ≤ 1 / 2 := hwle

-- reflection about the horizontal line Y = k/2 : (a,b) -> (a,-b), y -> k-y
private lemma csq_refl_v_fwd {x y a b k : ℝ} {p : ℝ × ℝ}
    (h : p ∈ csq x y a b) : (p.1, k - p.2) ∈ csq x (k - y) a (-b) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have e : a * (p.1 - x) + (-b) * ((k - p.2) - (k - y)) =
        a * (p.1 - x) + b * (p.2 - y) := by ring
    rw [e]; exact h1
  · have e : -(-b) * (p.1 - x) + a * ((k - p.2) - (k - y)) =
        -((-b) * (p.1 - x) + a * (p.2 - y)) := by ring
    rw [e, abs_neg]; exact h2

private lemma csq_refl_v_bwd {x y a b k : ℝ} {p : ℝ × ℝ}
    (h : (p.1, k - p.2) ∈ csq x (k - y) a (-b)) : p ∈ csq x y a b := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have e : a * (p.1 - x) + (-b) * ((k - p.2) - (k - y)) =
        a * (p.1 - x) + b * (p.2 - y) := by ring
    rw [e] at h1; exact h1
  · have e : -(-b) * (p.1 - x) + a * ((k - p.2) - (k - y)) =
        -((-b) * (p.1 - x) + a * (p.2 - y)) := by ring
    rw [e, abs_neg] at h2; exact h2

-- reflection about the vertical line X = k/2 : (a,b) -> (-a,b), x -> k-x
private lemma csq_refl_h_fwd {x y a b k : ℝ} {p : ℝ × ℝ}
    (h : p ∈ csq x y a b) : (k - p.1, p.2) ∈ csq (k - x) y (-a) b := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have e : (-a) * ((k - p.1) - (k - x)) + b * (p.2 - y) =
        a * (p.1 - x) + b * (p.2 - y) := by ring
    rw [e]; exact h1
  · have e : -b * ((k - p.1) - (k - x)) + (-a) * (p.2 - y) =
        -((-b) * (p.1 - x) + a * (p.2 - y)) := by ring
    rw [e, abs_neg]; exact h2

private lemma csq_refl_h_bwd {x y a b k : ℝ} {p : ℝ × ℝ}
    (h : (k - p.1, p.2) ∈ csq (k - x) y (-a) b) : p ∈ csq x y a b := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have e : (-a) * ((k - p.1) - (k - x)) + b * (p.2 - y) =
        a * (p.1 - x) + b * (p.2 - y) := by ring
    rw [e] at h1; exact h1
  · have e : -b * ((k - p.1) - (k - x)) + (-a) * (p.2 - y) =
        -((-b) * (p.1 - x) + a * (p.2 - y)) := by ring
    rw [e, abs_neg] at h2; exact h2

-- swap of the two coordinates: (a,b) -> (b,a), (x,y) -> (y,x)
private lemma csq_swap_fwd {x y a b : ℝ} {p : ℝ × ℝ}
    (h : p ∈ csq x y a b) : (p.2, p.1) ∈ csq y x b a := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have e : b * (p.2 - y) + a * (p.1 - x) = a * (p.1 - x) + b * (p.2 - y) := by ring
    rw [e]; exact h1
  · have e : -a * (p.2 - y) + b * (p.1 - x) = -((-b) * (p.1 - x) + a * (p.2 - y)) := by ring
    rw [e, abs_neg]; exact h2

private lemma csq_swap_bwd {x y a b : ℝ} {p : ℝ × ℝ}
    (h : (p.2, p.1) ∈ csq y x b a) : p ∈ csq x y a b := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have e : b * (p.2 - y) + a * (p.1 - x) = a * (p.1 - x) + b * (p.2 - y) := by ring
    rw [e] at h1; exact h1
  · have e : -a * (p.2 - y) + b * (p.1 - x) = -((-b) * (p.1 - x) + a * (p.2 - y)) := by ring
    rw [e, abs_neg] at h2; exact h2

-- the closed unit square contains the closed disk of radius 1/2 around its centre
private lemma disk_lemma (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (p : ℝ × ℝ)
    (hd : (p.1 - x) ^ 2 + (p.2 - y) ^ 2 ≤ 1 / 4) :
    |a * (p.1 - x) + b * (p.2 - y)| ≤ 1 / 2 ∧ |-b * (p.1 - x) + a * (p.2 - y)| ≤ 1 / 2 := by
  have hid1 : (a * (p.1 - x) + b * (p.2 - y)) ^ 2 +
      (a * (p.2 - y) - b * (p.1 - x)) ^ 2 = (p.1 - x) ^ 2 + (p.2 - y) ^ 2 := by
    have h2 : (a * (p.1 - x) + b * (p.2 - y)) ^ 2 +
        (a * (p.2 - y) - b * (p.1 - x)) ^ 2 =
        (a ^ 2 + b ^ 2) * ((p.1 - x) ^ 2 + (p.2 - y) ^ 2) := by ring
    rw [h2, hab, one_mul]
  have hid2 : (-b * (p.1 - x) + a * (p.2 - y)) ^ 2 +
      (a * (p.1 - x) + b * (p.2 - y)) ^ 2 = (p.1 - x) ^ 2 + (p.2 - y) ^ 2 := by
    have h2 : (-b * (p.1 - x) + a * (p.2 - y)) ^ 2 +
        (a * (p.1 - x) + b * (p.2 - y)) ^ 2 =
        (a ^ 2 + b ^ 2) * ((p.1 - x) ^ 2 + (p.2 - y) ^ 2) := by ring
    rw [h2, hab, one_mul]
  constructor
  · have h2 : (a * (p.1 - x) + b * (p.2 - y)) ^ 2 ≤ (1 / 2) ^ 2 := by
      nlinarith [sq_nonneg (a * (p.2 - y) - b * (p.1 - x))]
    exact abs_le_of_sq_le_sq h2 (by norm_num)
  · have h2 : (-b * (p.1 - x) + a * (p.2 - y)) ^ 2 ≤ (1 / 2) ^ 2 := by
      nlinarith [sq_nonneg (a * (p.1 - x) + b * (p.2 - y))]
    exact abs_le_of_sq_le_sq h2 (by norm_num)

private lemma exists_mul_half_abs (a : ℝ) :
    ∃ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), a * u = |a| / 2 := by
  rcases le_or_gt 0 a with ha | ha
  · exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by rw [abs_of_nonneg ha]; ring⟩
  · exact ⟨-(1 / 2), ⟨by norm_num, by norm_num⟩, by rw [abs_of_neg ha]; ring⟩

private lemma exists_mul_neg_half_abs (a : ℝ) :
    ∃ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), a * u = -(|a| / 2) := by
  rcases le_or_gt 0 a with ha | ha
  · exact ⟨-(1 / 2), ⟨by norm_num, by norm_num⟩, by rw [abs_of_nonneg ha]; ring⟩
  · exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by rw [abs_of_neg ha]; ring⟩

private lemma bbox_of_contain (x y a b k : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (h : csq x y a b ⊆ Set.Icc (0:ℝ) k ×ˢ Set.Icc (0:ℝ) k) :
    |a| + |b| ≤ 2 * x ∧ |a| + |b| ≤ 2 * (k - x) ∧
      |a| + |b| ≤ 2 * y ∧ |a| + |b| ≤ 2 * (k - y) := by
  have key : ∀ r s : ℝ, r ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) →
      s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) →
      (0 ≤ x + (a * r - b * s) ∧ x + (a * r - b * s) ≤ k) ∧
        (0 ≤ y + (b * r + a * s) ∧ y + (b * r + a * s) ≤ k) := by
    intro r s hr hs
    have hmem : ((x + (a * r - b * s), y + (b * r + a * s)) : ℝ × ℝ) ∈ csq x y a b := by
      constructor
      · have h1 : a * ((x + (a * r - b * s)) - x) + b * ((y + (b * r + a * s)) - y) = r := by
          have h2 : a * ((x + (a * r - b * s)) - x) + b * ((y + (b * r + a * s)) - y) =
              (a ^ 2 + b ^ 2) * r := by ring
          rw [h2, hab, one_mul]
        rw [h1]
        exact abs_le.mpr hr
      · have h1 : -b * ((x + (a * r - b * s)) - x) + a * ((y + (b * r + a * s)) - y) = s := by
          have h2 : -b * ((x + (a * r - b * s)) - x) + a * ((y + (b * r + a * s)) - y) =
              (a ^ 2 + b ^ 2) * s := by ring
          rw [h2, hab, one_mul]
        rw [h1]
        exact abs_le.mpr hs
    have hp := h hmem
    simpa only [Set.mem_prod, Set.mem_Icc] using hp
  have h1 := key _ _ (exists_mul_neg_half_abs a).choose_spec.1 (exists_mul_half_abs b).choose_spec.1
  have h2 := key _ _ (exists_mul_half_abs a).choose_spec.1 (exists_mul_neg_half_abs b).choose_spec.1
  have h3 := key _ _ (exists_mul_neg_half_abs b).choose_spec.1 (exists_mul_neg_half_abs a).choose_spec.1
  have h4 := key _ _ (exists_mul_half_abs b).choose_spec.1 (exists_mul_half_abs a).choose_spec.1
  obtain ⟨u1, hu1, hue1⟩ := exists_mul_neg_half_abs a
  obtain ⟨v1, hv1, hve1⟩ := exists_mul_half_abs b
  have hk1 : (0 ≤ x + (a * u1 - b * v1) ∧ x + (a * u1 - b * v1) ≤ k) ∧
      (0 ≤ y + (b * u1 + a * v1) ∧ y + (b * u1 + a * v1) ≤ k) := key u1 v1 hu1 hv1
  have hc1 : a * u1 - b * v1 = -((|a| + |b|) / 2) := by linarith
  obtain ⟨u2, hu2, hue2⟩ := exists_mul_half_abs a
  obtain ⟨v2, hv2, hve2⟩ := exists_mul_neg_half_abs b
  have hk2 := key u2 v2 hu2 hv2
  have hc2 : a * u2 - b * v2 = (|a| + |b|) / 2 := by linarith
  obtain ⟨u3, hu3, hue3⟩ := exists_mul_neg_half_abs b
  obtain ⟨v3, hv3, hve3⟩ := exists_mul_neg_half_abs a
  have hk3 := key u3 v3 hu3 hv3
  have hc3 : b * u3 + a * v3 = -((|a| + |b|) / 2) := by linarith
  obtain ⟨u4, hu4, hue4⟩ := exists_mul_half_abs b
  obtain ⟨v4, hv4, hve4⟩ := exists_mul_half_abs a
  have hk4 := key u4 v4 hu4 hv4
  have hc4 : b * u4 + a * v4 = (|a| + |b|) / 2 := by linarith
  refine ⟨by linarith [hk1.1.1, hc1], by linarith [hk2.1.2, hc2],
    by linarith [hk3.2.1, hc3], by linarith [hk4.2.2, hc4]⟩
end


/-- 两个平方和 ≤ 1/4 ⇒ 各自绝对值 ≤ 1/2。 -/
private lemma sq_pair_bound (P Q : ℝ) (h : P ^ 2 + Q ^ 2 ≤ (1 / 4 : ℝ)) :
    |P| ≤ 1 / 2 ∧ |Q| ≤ 1 / 2 := by
  have h1 : P ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by nlinarith [h, sq_nonneg Q]
  have h2 : Q ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by nlinarith [h, sq_nonneg P]
  refine ⟨?_, ?_⟩
  · have hh := sq_le_sq.mp h1
    simpa using hh
  · have hh := sq_le_sq.mp h2
    simpa using hh

/-- 三个二次式中至少一个 ≤ 1/2 的纯代数引理。 -/
private lemma tri_quad_aux (t1 t2 t3 : ℝ) (h1n : 0 ≤ t1) (h2n : 0 ≤ t2) (h3n : 0 ≤ t3)
    (hsum : t1 + t2 + t3 = 1) :
    (t2 + t3) ^ 2 + t3 ^ 2 ≤ 1 / 2 ∨ t1 ^ 2 + t3 ^ 2 ≤ 1 / 2 ∨
      t1 ^ 2 + (t1 + t2) ^ 2 ≤ 1 / 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨hA, hB, hC⟩ := hc
  rcases eq_or_lt_of_le h1n with h1z | h1p
  · -- t1 = 0
    have hB' : (1:ℝ) / 2 < t3 ^ 2 := by nlinarith [hB, h1z]
    have hC' : (1:ℝ) / 2 < t2 ^ 2 := by nlinarith [hC, h1z]
    have hs : t2 + t3 = 1 := by linarith
    nlinarith [hB', hC', hs, h2n, h3n, sq_nonneg (t2 - t3)]
  rcases eq_or_lt_of_le h3n with h3z | h3p
  · -- t3 = 0
    have hA' : (1:ℝ) / 2 < t2 ^ 2 := by nlinarith [hA, h3z]
    have hB' : (1:ℝ) / 2 < t1 ^ 2 := by nlinarith [hB, h3z]
    have hs : t1 + t2 = 1 := by linarith
    nlinarith [hA', hB', hs, h1n, h2n, sq_nonneg (t1 - t2)]
  · -- t1, t3 > 0
    have hA2 : t3 ^ 2 > t1 * (1 - t1) := by nlinarith [hA, hB, hsum]
    have hB2 : t1 ^ 2 > t3 * (1 - t3) := by nlinarith [hB, hC, hsum]
    have hlt1 : t1 < t3 := by nlinarith [hA2, h1p, h3p, hsum, h2n]
    have hlt2 : t3 < t1 := by nlinarith [hB2, h1p, h3p, hsum, h2n]
    linarith

/-- 引理3 的核心代数部分：三角形 {0 ≤ Y ≤ X ≤ r}（r=√2/2）内的中心。 -/
private lemma five_lemma3_tri (X Y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hYX : Y ≤ X)
    (hXr : X ≤ Real.sqrt 2 / 2) (hYr : Y ≤ Real.sqrt 2 / 2) :
    (|-a * X + b * (-Y)| ≤ 1 / 2 ∧ |b * X + a * (-Y)| ≤ 1 / 2) ∨
    (|a * (Real.sqrt 2 / 2 - X) + b * (-Y)| ≤ 1 / 2 ∧
      |-b * (Real.sqrt 2 / 2 - X) + a * (-Y)| ≤ 1 / 2) ∨
    (|a * (Real.sqrt 2 / 2 - X) + b * (Real.sqrt 2 / 2 - Y)| ≤ 1 / 2 ∧
      |-b * (Real.sqrt 2 / 2 - X) + a * (Real.sqrt 2 / 2 - Y)| ≤ 1 / 2) := by
  classical
  set r : ℝ := Real.sqrt 2 / 2 with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrne : r ≠ 0 := hrpos.ne'
  have hr2 : r ^ 2 = 1 / 2 := by
    rw [hr]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  set t3 : ℝ := Y / r with ht3
  set t2 : ℝ := X / r - Y / r with ht2
  set t1 : ℝ := 1 - X / r with ht1
  have ht1n : 0 ≤ t1 := by rw [ht1]; rw [sub_nonneg]; rw [div_le_one hrpos]; linarith
  have ht2n : 0 ≤ t2 := by
    rw [ht2]; rw [sub_nonneg]; exact div_le_div_of_nonneg_right hYX hrpos.le
  have ht3n : 0 ≤ t3 := by rw [ht3]; positivity
  have hsum : t1 + t2 + t3 = 1 := by rw [ht1, ht2, ht3]; field_simp; ring
  have hXeq : X = r * (t2 + t3) := by rw [ht2, ht3]; field_simp; ring
  have hYeq : Y = r * t3 := by rw [ht3]; field_simp
  have ht1r : r * t1 = r - X := by rw [ht1]; field_simp
  have ht12r : r * (t1 + t2) = r - Y := by rw [ht1, ht2]; field_simp; ring
  have key := tri_quad_aux t1 t2 t3 ht1n ht2n ht3n hsum
  rcases key with hS1 | hS2 | hS3
  · -- 顶点 (1,1)
    left
    have hX' : X = r * (t2 + t3) := hXeq
    have hY' : Y = r * t3 := hYeq
    have hAB : (-a * X + b * (-Y)) ^ 2 + (b * X + a * (-Y)) ^ 2
        = r ^ 2 * ((t2 + t3) ^ 2 + t3 ^ 2) := by
      rw [hX', hY']
      rw [show (-a * (r * (t2 + t3)) + b * (-(r * t3))) ^ 2 +
          (b * (r * (t2 + t3)) + a * (-(r * t3))) ^ 2
          = r ^ 2 * ((a * (t2 + t3) + b * t3) ^ 2 + (b * (t2 + t3) - a * t3) ^ 2) by ring]
      congr 1
      linear_combination ((t2 + t3) ^ 2 + t3 ^ 2) * hab
    have hbound : (-a * X + b * (-Y)) ^ 2 + (b * X + a * (-Y)) ^ 2 ≤ 1 / 4 := by
      rw [hAB]
      nlinarith [hr2, hS1]
    exact ⟨(sq_pair_bound _ _ hbound).1, (sq_pair_bound _ _ hbound).2⟩
  · -- 顶点 (1+r, 1)
    right; left
    have hA : r - X = r * t1 := by rw [ht1r]
    have hY' : Y = r * t3 := hYeq
    have hAB : (a * (r - X) + b * (-Y)) ^ 2 + ((-b) * (r - X) + a * (-Y)) ^ 2
        = r ^ 2 * (t1 ^ 2 + t3 ^ 2) := by
      rw [hA, hY']
      rw [show (a * (r * t1) + b * (-(r * t3))) ^ 2 + ((-b) * (r * t1) + a * (-(r * t3))) ^ 2
          = r ^ 2 * ((a * t1 - b * t3) ^ 2 + (b * t1 + a * t3) ^ 2) by ring]
      congr 1
      linear_combination (t1 ^ 2 + t3 ^ 2) * hab
    have hbound : (a * (r - X) + b * (-Y)) ^ 2 + ((-b) * (r - X) + a * (-Y)) ^ 2 ≤ 1 / 4 := by
      rw [hAB]
      nlinarith [hr2, hS2]
    exact ⟨(sq_pair_bound _ _ hbound).1, (sq_pair_bound _ _ hbound).2⟩
  · -- 顶点 (1+r, 1+r)
    right; right
    have hX' : r - X = r * t1 := ht1r.symm
    have hY' : r - Y = r * (t1 + t2) := ht12r.symm
    have hAB : (a * (r - X) + b * (r - Y)) ^ 2 + ((-b) * (r - X) + a * (r - Y)) ^ 2
        = r ^ 2 * (t1 ^ 2 + (t1 + t2) ^ 2) := by
      rw [hX', hY']
      rw [show (a * (r * t1) + b * (r * (t1 + t2))) ^ 2 +
          ((-b) * (r * t1) + a * (r * (t1 + t2))) ^ 2
          = r ^ 2 * ((a * t1 + b * (t1 + t2)) ^ 2 + (b * t1 - a * (t1 + t2)) ^ 2) by ring]
      congr 1
      linear_combination (t1 ^ 2 + (t1 + t2) ^ 2) * hab
    have hbound : (a * (r - X) + b * (r - Y)) ^ 2 + ((-b) * (r - X) + a * (r - Y)) ^ 2 ≤ 1 / 4 := by
      rw [hAB]
      nlinarith [hr2, hS3]
    exact ⟨(sq_pair_bound _ _ hbound).1, (sq_pair_bound _ _ hbound).2⟩

/-- 引理3（右下三角形）：中心在 conv{(1,1),(1+r,1),(1+r,1+r)} 内 ⇒ 含 P 中一点。 -/
private lemma five_lemma3_lowerright (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hyx : y ≤ x) (hx2 : x ≤ 1 + Real.sqrt 2 / 2) :
    (1, 1) ∈ csq x y a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq x y a b ∨
      (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2) ∈ csq x y a b := by
  set r : ℝ := Real.sqrt 2 / 2 with hr
  have hres := five_lemma3_tri (x - 1) (y - 1) a b hab
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨?_, ?_⟩
    · convert h1 using 2 <;> ring
    · convert h2 using 2 <;> ring
  · right; left
    refine ⟨?_, ?_⟩
    · convert h1 using 2 <;> ring
    · convert h2 using 2 <;> ring
  · right; right
    refine ⟨?_, ?_⟩
    · convert h1 using 2 <;> ring
    · convert h2 using 2 <;> ring


noncomputable section

/-- helper: 从「反射后中心」的方框包含得原方框包含。 -/
private lemma box_refl_h {x y a b : ℝ}
    (hbox : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk) :
    csq (kk - x) y (-a) b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk := by
  intro q hq
  have h1 : (kk - q.1, q.2) ∈ csq x y a b :=
    csq_refl_h_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
      (p := (kk - q.1, q.2)) (by
        have e : kk - (kk - q.1) = q.1 := by ring
        rw [e]; exact hq)
  have h2 := hbox h1
  rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at h2 ⊢
  exact ⟨⟨by linarith [h2.1.2], by linarith [h2.1.1]⟩, h2.2⟩

private lemma box_refl_v {x y a b : ℝ}
    (hbox : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk) :
    csq x (kk - y) a (-b) ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk := by
  intro q hq
  have h1 : (q.1, kk - q.2) ∈ csq x y a b :=
    csq_refl_v_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
      (p := (q.1, kk - q.2)) (by
        have e : kk - (kk - q.2) = q.2 := by ring
        rw [e]; exact hq)
  have h2 := hbox h1
  rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at h2 ⊢
  exact ⟨h2.1, ⟨by linarith [h2.2.2], by linarith [h2.2.1]⟩⟩

private lemma box_swap {x y a b : ℝ}
    (hbox : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk) :
    csq y x b a ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk := by
  intro q hq
  have h1 : (q.2, q.1) ∈ csq x y a b :=
    csq_swap_bwd (x := x) (y := y) (a := a) (b := b) (p := (q.2, q.1)) (by
      simpa using hq)
  have h2 := hbox h1
  rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at h2 ⊢
  exact ⟨h2.2, h2.1⟩

/-- 由中心位置得方框条件（bbox_of_contain 的包装）。 -/
private lemma bbox_bounds {x y a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk) :
    |a| + |b| ≤ 2 * x ∧ |a| + |b| ≤ 2 * (kk - x) ∧
      |a| + |b| ≤ 2 * y ∧ |a| + |b| ≤ 2 * (kk - y) :=
  bbox_of_contain x y a b kk hab hsub

/-- 中心在 [0,kk]^2（由方框包含得）。 -/
private lemma center_bounds {x y a b : ℝ}
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk) :
    0 ≤ x ∧ x ≤ kk ∧ 0 ≤ y ∧ y ≤ kk := by
  have h0 : (x, y) ∈ csq x y a b := by
    constructor <;> simp
  have h := hsub h0
  rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

/-- Friedman 引理1 的 bbox 形式，给出 (1,1) ∈ csq。 -/
private lemma corner_LL (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    (1, 1) ∈ csq x y a b := by
  have hb := bbox_bounds hab hsub
  exact corner_lemma x y a b hab hb.1 hb.2.2.1 hx1 hy1

/-- 右下角：中心在 [kk-1,kk]×[0,1]，含 (kk-1,1)。 -/
private lemma corner_LR (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hx0 : kk - 1 ≤ x) (hx1 : x ≤ kk) (hy1 : y ≤ 1) :
    (1 + Real.sqrt 2 / 2, 1) ∈ csq x y a b := by
  have hk1 : kk - 1 = 1 + Real.sqrt 2 / 2 := by unfold kk; ring
  have hsub' : csq (kk - x) y (-a) b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk := by
    intro q hq
    have h1 : (kk - q.1, q.2) ∈ csq x y a b :=
      csq_refl_h_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
        (p := (kk - q.1, q.2)) (by simpa using hq)
    have h2 := hsub h1
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at h2 ⊢
    exact ⟨⟨by linarith [h2.1.2], by linarith [h2.1.1]⟩, h2.2⟩
  have hc := corner_LL (kk - x) y (-a) b (by nlinarith [hab]) hsub'
    (by linarith) (by linarith)
  have h2 : (kk - 1, 1) ∈ csq x y a b :=
    csq_refl_h_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
      (p := (kk - 1, 1)) (by
        have e : kk - (kk - 1) = 1 := by ring
        rw [e]; exact hc)
  rw [← hk1]
  simpa using h2

/-- 左上角：中心在 [0,1]×[kk-1,kk]，含 (1,kk-1)。 -/
private lemma corner_UL (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hx1 : x ≤ 1) (hy0 : kk - 1 ≤ y) (hy1 : y ≤ kk) :
    (1, 1 + Real.sqrt 2 / 2) ∈ csq x y a b := by
  have hk1 : kk - 1 = 1 + Real.sqrt 2 / 2 := by unfold kk; ring
  have hsub' : csq x (kk - y) a (-b) ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk := by
    intro q hq
    have h1 : (q.1, kk - q.2) ∈ csq x y a b :=
      csq_refl_v_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
        (p := (q.1, kk - q.2)) (by simpa using hq)
    have h2 := hsub h1
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at h2 ⊢
    exact ⟨h2.1, ⟨by linarith [h2.2.2], by linarith [h2.2.1]⟩⟩
  have hc := corner_LL x (kk - y) a (-b) (by nlinarith [hab]) hsub'
    (by linarith) (by linarith)
  have h2 : (1, kk - 1) ∈ csq x y a b :=
    csq_refl_v_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
      (p := (1, kk - 1)) (by
        have e : kk - (kk - 1) = 1 := by ring
        rw [e]; exact hc)
  rw [← hk1]
  simpa using h2

/-- 右上角：中心在 [kk-1,kk]^2，含 (kk-1,kk-1)。 -/
private lemma corner_UR (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hx0 : kk - 1 ≤ x) (hx1 : x ≤ kk) (hy0 : kk - 1 ≤ y) (hy1 : y ≤ kk) :
    (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2) ∈ csq x y a b := by
  have hk1 : kk - 1 = 1 + Real.sqrt 2 / 2 := by unfold kk; ring
  have hsub1 : csq (kk - x) y (-a) b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk := by
    intro q hq
    have h1 : (kk - q.1, q.2) ∈ csq x y a b :=
      csq_refl_h_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
        (p := (kk - q.1, q.2)) (by simpa using hq)
    have h2 := hsub h1
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at h2 ⊢
    exact ⟨⟨by linarith [h2.1.2], by linarith [h2.1.1]⟩, h2.2⟩
  have hsub2 : csq (kk - x) (kk - y) (-a) (-b) ⊆
      Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk := by
    intro q hq
    have h1 : (q.1, kk - q.2) ∈ csq (kk - x) y (-a) b :=
      csq_refl_v_bwd (k := kk) (x := kk - x) (y := y) (a := -a) (b := b)
        (p := (q.1, kk - q.2)) (by simpa using hq)
    have h2 := hsub1 h1
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at h2 ⊢
    exact ⟨h2.1, ⟨by linarith [h2.2.2], by linarith [h2.2.1]⟩⟩
  have hc := corner_LL (kk - x) (kk - y) (-a) (-b) (by nlinarith [hab]) hsub2
    (by linarith) (by linarith)
  have h2 : (1, kk - 1) ∈ csq (kk - x) y (-a) b :=
    csq_refl_v_bwd (k := kk) (x := kk - x) (y := y) (a := -a) (b := b)
      (p := (1, kk - 1)) (by
        have e : kk - (kk - 1) = 1 := by ring
        rw [e]; exact hc)
  have h3 : (kk - 1, kk - 1) ∈ csq x y a b :=
    csq_refl_h_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
      (p := (kk - 1, kk - 1)) (by
        have e : kk - (kk - 1) = 1 := by ring
        simpa [e] using h2)
  rw [← hk1]
  have e2 : kk - 1 = 1 + Real.sqrt 2 / 2 := hk1
  convert h3 using 2 <;> exact e2.symm


/-- 底边条情形（用 hlemma2）。 -/
private lemma region_bottom (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hlemma2 : ∀ (cx cy a b : ℝ), a ^ 2 + b ^ 2 = 1 →
      csq cx cy a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk →
      1 ≤ cx → cx ≤ 1 + Real.sqrt 2 / 2 → 0 ≤ cy → cy ≤ 1 →
      (1, 1) ∈ csq cx cy a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq cx cy a b)
    (hx1 : 1 ≤ x) (hx2 : x ≤ kk - 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1, 1) ∈ csq x y a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq x y a b := by
  have hkx : x ≤ 1 + Real.sqrt 2 / 2 := by
    have : kk - 1 = 1 + Real.sqrt 2 / 2 := by unfold kk; ring
    linarith
  exact hlemma2 x y a b hab hsub hx1 hkx hy0 hy1

/-- 顶边条情形。 -/
private lemma region_top (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hlemma2 : ∀ (cx cy a b : ℝ), a ^ 2 + b ^ 2 = 1 →
      csq cx cy a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk →
      1 ≤ cx → cx ≤ 1 + Real.sqrt 2 / 2 → 0 ≤ cy → cy ≤ 1 →
      (1, 1) ∈ csq cx cy a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq cx cy a b)
    (hx1 : 1 ≤ x) (hx2 : x ≤ kk - 1) (hy0 : kk - 1 ≤ y) (hy1 : y ≤ kk) :
    (1, 1 + Real.sqrt 2 / 2) ∈ csq x y a b ∨
      (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2) ∈ csq x y a b := by
  have hk1 : kk - 1 = 1 + Real.sqrt 2 / 2 := by unfold kk; ring
  have hsub' : csq x (kk - y) a (-b) ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk :=
    box_refl_v (x := x) (y := y) (a := a) (b := b) hsub
  have hy'0 : 0 ≤ kk - y := by linarith
  have hy'1 : kk - y ≤ 1 := by linarith
  have h := region_bottom x (kk - y) a (-b) (by nlinarith [hab]) hsub' hlemma2
    hx1 hx2 hy'0 hy'1
  rcases h with h | h
  · left
    have e : (1, kk - 1) ∈ csq x y a b :=
      csq_refl_v_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
        (p := (1, kk - 1)) (by
          have ee : kk - (kk - 1) = 1 := by ring
          rw [ee]; exact h)
    rw [← hk1]
    simpa using e
  · right
    have h' : (kk - 1, 1) ∈ csq x (kk - y) a (-b) := by
      rw [hk1]; exact h
    have e : (kk - 1, kk - 1) ∈ csq x y a b :=
      csq_refl_v_bwd (k := kk) (x := x) (y := y) (a := a) (b := b)
        (p := (kk - 1, kk - 1)) (by
          have ee : kk - (kk - 1) = 1 := by ring
          rw [ee]; exact h')
    rw [← hk1]
    exact e

/-- 左边条情形。 -/
private lemma region_left (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hlemma2 : ∀ (cx cy a b : ℝ), a ^ 2 + b ^ 2 = 1 →
      csq cx cy a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk →
      1 ≤ cx → cx ≤ 1 + Real.sqrt 2 / 2 → 0 ≤ cy → cy ≤ 1 →
      (1, 1) ∈ csq cx cy a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq cx cy a b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy1 : 1 ≤ y) (hy2 : y ≤ kk - 1) :
    (1, 1) ∈ csq x y a b ∨ (1, 1 + Real.sqrt 2 / 2) ∈ csq x y a b := by
  have hk1 : kk - 1 = 1 + Real.sqrt 2 / 2 := by unfold kk; ring
  have hsub' : csq y x b a ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk :=
    box_swap (x := x) (y := y) (a := a) (b := b) hsub
  have h := region_bottom y x b a (by nlinarith [hab]) hsub' hlemma2 hy1 hy2 hx0 hx1
  rcases h with h | h
  · left
    exact csq_swap_bwd (x := x) (y := y) (a := a) (b := b) (p := (1, 1)) (by
      simpa using h)
  · right
    have e : (1, 1 + Real.sqrt 2 / 2) ∈ csq x y a b :=
      csq_swap_bwd (x := x) (y := y) (a := a) (b := b)
        (p := (1, 1 + Real.sqrt 2 / 2)) (by
          have ee : (1, 1 + Real.sqrt 2 / 2) = ((1 + Real.sqrt 2 / 2, 1) : ℝ × ℝ).swap := by
            simp
          rw [ee]
          simpa using h)
    exact e

/-- 右边条情形。 -/
private lemma region_right (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hsub : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hlemma2 : ∀ (cx cy a b : ℝ), a ^ 2 + b ^ 2 = 1 →
      csq cx cy a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk →
      1 ≤ cx → cx ≤ 1 + Real.sqrt 2 / 2 → 0 ≤ cy → cy ≤ 1 →
      (1, 1) ∈ csq cx cy a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq cx cy a b)
    (hx0 : kk - 1 ≤ x) (hx1 : x ≤ kk) (hy1 : 1 ≤ y) (hy2 : y ≤ kk - 1) :
    (1 + Real.sqrt 2 / 2, 1) ∈ csq x y a b ∨
      (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2) ∈ csq x y a b := by
  have hk1 : kk - 1 = 1 + Real.sqrt 2 / 2 := by unfold kk; ring
  have hsub' : csq y x b a ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk :=
    box_swap (x := x) (y := y) (a := a) (b := b) hsub
  have h := region_top y x b a (by nlinarith [hab]) hsub' hlemma2 hy1 hy2 hx0 hx1
  rcases h with h | h
  · left
    have e : (1 + Real.sqrt 2 / 2, 1) ∈ csq x y a b :=
      csq_swap_bwd (x := x) (y := y) (a := a) (b := b)
        (p := (1 + Real.sqrt 2 / 2, 1)) (by
          have ee : (1 + Real.sqrt 2 / 2, 1) = ((1, 1 + Real.sqrt 2 / 2) : ℝ × ℝ).swap := by
            simp
          rw [ee]
          simpa using h)
    exact e
  · right
    have h' : (kk - 1, kk - 1) ∈ csq y x b a := by
      rw [hk1]; exact h
    have e : (kk - 1, kk - 1) ∈ csq x y a b :=
      csq_swap_bwd (x := x) (y := y) (a := a) (b := b)
        (p := (kk - 1, kk - 1)) (by simpa using h')
    rw [← hk1]
    exact e

/-- 中心区域（用引理3：中心方块的对角线三角剖分）。 -/
private lemma region_center (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hx1 : 1 ≤ x) (hx2 : x ≤ kk - 1) (hy1 : 1 ≤ y) (hy2 : y ≤ kk - 1) :
    (1, 1) ∈ csq x y a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq x y a b ∨
      (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2) ∈ csq x y a b ∨
      (1, 1 + Real.sqrt 2 / 2) ∈ csq x y a b := by
  have hk1 : kk - 1 = 1 + Real.sqrt 2 / 2 := by unfold kk; ring
  have hx2' : x ≤ 1 + Real.sqrt 2 / 2 := by linarith
  have hy2' : y ≤ 1 + Real.sqrt 2 / 2 := by linarith
  rcases le_or_gt y x with hyx | hyx
  · have h := five_lemma3_lowerright x y a b hab hx1 hy1 hyx hx2'
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · -- x < y：交换后用引理3
    have h := five_lemma3_lowerright y x b a (by nlinarith [hab]) hy1 hx1 hyx.le hy2'
    rcases h with h | h | h
    · exact Or.inl (csq_swap_bwd (x := x) (y := y) (a := a) (b := b) (p := (1, 1)) (by
        simpa using h))
    · have e : (1, 1 + Real.sqrt 2 / 2) ∈ csq x y a b :=
        csq_swap_bwd (x := x) (y := y) (a := a) (b := b)
          (p := (1, 1 + Real.sqrt 2 / 2)) (by
            have ee : (1, 1 + Real.sqrt 2 / 2) = ((1 + Real.sqrt 2 / 2, 1) : ℝ × ℝ).swap := by
              simp
            rw [ee]
            simpa using h)
      exact Or.inr (Or.inr (Or.inr e))
    · have e : (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2) ∈ csq x y a b :=
        csq_swap_bwd (x := x) (y := y) (a := a) (b := b)
          (p := (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2)) (by
            have ee : (1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2) =
                ((1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2) : ℝ × ℝ).swap := by simp
            rw [ee]
            exact h)
      exact Or.inr (Or.inr (Or.inl e))

/-- pset 成员资格辅助。 -/
private lemma mem_pset_11 : ((1:ℝ), (1:ℝ)) ∈ pset := by unfold pset; simp
private lemma mem_pset_1r : ((1:ℝ), (1 + Real.sqrt 2 / 2)) ∈ pset := by unfold pset; simp
private lemma mem_pset_r1 : ((1 + Real.sqrt 2 / 2 : ℝ), (1:ℝ)) ∈ pset := by unfold pset; simp
private lemma mem_pset_rr : ((1 + Real.sqrt 2 / 2 : ℝ), (1 + Real.sqrt 2 / 2)) ∈ pset := by
  unfold pset; simp

/-- 不可避免点引理（组装版）：任意含于 [0,kk]^2 的单位闭正方形含 P 中一点。 -/
private lemma five_unavoidable
    (hlemma2 : ∀ (cx cy a b : ℝ), a ^ 2 + b ^ 2 = 1 →
      csq cx cy a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk →
      1 ≤ cx → cx ≤ 1 + Real.sqrt 2 / 2 → 0 ≤ cy → cy ≤ 1 →
      (1, 1) ∈ csq cx cy a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq cx cy a b) :
    ∀ x y a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk →
      ∃ p ∈ pset, p ∈ csq x y a b := by
  intro x y a b hab hsub
  obtain ⟨hx0, hxkk, hy0, hykk⟩ := center_bounds hsub
  rcases le_or_gt x 1 with hx1 | hx1
  · rcases le_or_gt y 1 with hy1 | hy1
    · -- 左下角
      exact ⟨(1, 1), mem_pset_11, corner_LL x y a b hab hsub hx1 hy1⟩
    · rcases le_or_gt (kk - 1) y with hy2 | hy2
      · -- 左上角
        exact ⟨(1, 1 + Real.sqrt 2 / 2), mem_pset_1r,
          corner_UL x y a b hab hsub hx1 hy2 hykk⟩
      · -- 左边条
        rcases region_left x y a b hab hsub hlemma2 hx0 hx1 hy1.le hy2.le with h | h
        · exact ⟨(1, 1), mem_pset_11, h⟩
        · exact ⟨(1, 1 + Real.sqrt 2 / 2), mem_pset_1r, h⟩
  · rcases le_or_gt x (kk - 1) with hx2 | hx2
    · rcases le_or_gt y 1 with hy1 | hy1
      · -- 底边条
        rcases region_bottom x y a b hab hsub hlemma2 hx1.le hx2 hy0 hy1 with h | h
        · exact ⟨(1, 1), mem_pset_11, h⟩
        · exact ⟨(1 + Real.sqrt 2 / 2, 1), mem_pset_r1, h⟩
      · rcases le_or_gt (kk - 1) y with hy2 | hy2
        · -- 顶边条
          rcases region_top x y a b hab hsub hlemma2 hx1.le hx2 hy2 hykk with h | h
          · exact ⟨(1, 1 + Real.sqrt 2 / 2), mem_pset_1r, h⟩
          · exact ⟨(1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2), mem_pset_rr, h⟩
        · -- 中心
          rcases region_center x y a b hab hx1.le hx2 hy1.le hy2.le with h | h | h | h
          · exact ⟨(1, 1), mem_pset_11, h⟩
          · exact ⟨(1 + Real.sqrt 2 / 2, 1), mem_pset_r1, h⟩
          · exact ⟨(1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2), mem_pset_rr, h⟩
          · exact ⟨(1, 1 + Real.sqrt 2 / 2), mem_pset_1r, h⟩
    · rcases le_or_gt y 1 with hy1 | hy1
      · -- 右下角
        exact ⟨(1 + Real.sqrt 2 / 2, 1), mem_pset_r1,
          corner_LR x y a b hab hsub hx2.le hxkk hy1⟩
      · rcases le_or_gt y (kk - 1) with hy2 | hy2
        · -- 右边条
          rcases region_right x y a b hab hsub hlemma2 hx2.le hxkk hy1.le hy2 with h | h
          · exact ⟨(1 + Real.sqrt 2 / 2, 1), mem_pset_r1, h⟩
          · exact ⟨(1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2), mem_pset_rr, h⟩
        · -- 右上角
          exact ⟨(1 + Real.sqrt 2 / 2, 1 + Real.sqrt 2 / 2), mem_pset_rr,
            corner_UR x y a b hab hsub hx2.le hxkk hy2.le hykk⟩

private lemma key_ineq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (hsp : Real.sqrt 2 ^ 2 = 2) :
    a * b * (Real.sqrt 2 / 2) ≤ a + b - 1 := by
  have hw : a + b ≤ Real.sqrt 2 := by
    have h2 : (a + b) ^ 2 ≤ 2 := by nlinarith [hab, sq_nonneg (a - b)]
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [h2, hsp, hs, sq_nonneg (a + b - Real.sqrt 2), sq_nonneg (a + b), ha, hb]
  have hfac : a * b * (Real.sqrt 2 / 2) = (a + b - 1) * (Real.sqrt 2 / 2 * (a + b + 1) / 2) := by
    have h2 : (a + b - 1) * (a + b + 1) = 2 * (a * b) := by nlinarith [hab]
    have e1 : a * b * (Real.sqrt 2 / 2) = (Real.sqrt 2 / 2) * (a * b) := by ring
    have e2 : (a + b - 1) * (Real.sqrt 2 / 2 * (a + b + 1) / 2) =
        (Real.sqrt 2 / 2) * ((a + b - 1) * (a + b + 1)) / 2 := by ring
    rw [e1, e2, h2]
    ring
  have hr2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by nlinarith [hsp]
  have hsmall : Real.sqrt 2 / 2 * (a + b + 1) / 2 ≤ 1 := by
    nlinarith [hw, hr2, Real.sqrt_nonneg 2]
  have hnonneg : 0 ≤ a + b - 1 := by
    nlinarith [hab, sq_nonneg (a - b), ha, hb]
  nlinarith [hfac, hsmall, hnonneg]

-- case A: au - bq > 1/2
private lemma l2_case_A (a b u q : ℝ) (hsp : Real.sqrt 2 ^ 2 = 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (hu0 : 0 ≤ u) (hur : u ≤ Real.sqrt 2 / 2)
    (hq0 : 0 ≤ q) (hqb : q ≤ 1 - (a + b) / 2)
    (hA : 1 / 2 < a * u - b * q) :
    b * q + a * (Real.sqrt 2 / 2 - u) ≤ 1 / 2 ∧
      b * (Real.sqrt 2 / 2 - u) - a * q ≤ 1 / 2 := by
  have hr1 : Real.sqrt 2 / 2 < 1 := by nlinarith [hsp, Real.sqrt_nonneg 2]
  have ha1 : a ≤ 1 := by nlinarith [hab, ha, sq_nonneg b]
  have har : 1 / 2 < a * (Real.sqrt 2 / 2) := by nlinarith [hA, hu0, hur, ha, hq0, hb]
  have har2 : a * (Real.sqrt 2 / 2) ≤ 1 := by nlinarith [ha1, hr1, ha]
  have hbr : b * (Real.sqrt 2 / 2) < 1 / 2 := by
    nlinarith [har, hsp, hab, ha, hb, sq_nonneg a, sq_nonneg b]
  constructor
  · nlinarith [hA, har, hur, ha, har2]
  · nlinarith [hbr, hur, ha, hb, hq0]

-- case B: bu + aq > 1/2
private lemma l2_case_B (a b u q : ℝ) (hsp : Real.sqrt 2 ^ 2 = 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (hu0 : 0 ≤ u) (hur : u ≤ Real.sqrt 2 / 2)
    (hq0 : 0 ≤ q) (hqb : q ≤ 1 - (a + b) / 2)
    (hB : 1 / 2 < b * u + a * q) :
    b * q + a * (Real.sqrt 2 / 2 - u) ≤ 1 / 2 ∧
      b * (Real.sqrt 2 / 2 - u) - a * q ≤ 1 / 2 := by
  have hr : 0 < Real.sqrt 2 / 2 := by positivity
  have hr2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by nlinarith [hsp]
  have ha1 : a ≤ 1 := by nlinarith [hab, ha, sq_nonneg b]
  have hb1 : b ≤ 1 := by nlinarith [hab, hb, sq_nonneg a]
  constructor
  · by_cases ha0 : a = 0
    · subst ha0
      have hb1' : b = 1 := by nlinarith [hab, hb]
      rw [hb1'] at *
      have hq2 : q ≤ 1 / 2 := by nlinarith [hqb]
      nlinarith [hB, hur, hr, hq2]
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      by_cases hb0 : b = 0
      · subst hb0
        have ha1' : a = 1 := by nlinarith [hab, ha]
        rw [ha1'] at *
        nlinarith [hur, hr]
      · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hmul : a / 2 < a * (b * u + a * q) := by nlinarith [hB, hapos]
        have hkey := key_ineq a b ha hb hab hsp
        have hmul2 : b * (b * q + a * (Real.sqrt 2 / 2 - u)) < b / 2 := by
          nlinarith [hmul, hkey, hqb, hab, hr2]
        nlinarith [hmul2, hbpos]
  · nlinarith [hB, hb1, hr, hq0, ha]

-- b >= 0 branch of the Lemma 2 core
private lemma l2_pos (a b u q : ℝ) (hsp : Real.sqrt 2 ^ 2 = 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (hu0 : 0 ≤ u) (hur : u ≤ Real.sqrt 2 / 2)
    (hq0 : 0 ≤ q) (hqb : q ≤ 1 - (a + b) / 2) :
    (|b * q - a * u| ≤ 1 / 2 ∧ |b * u + a * q| ≤ 1 / 2) ∨
    (|b * q + a * (Real.sqrt 2 / 2 - u)| ≤ 1 / 2 ∧
      |a * q - b * (Real.sqrt 2 / 2 - u)| ≤ 1 / 2) := by
  have hr : 0 < Real.sqrt 2 / 2 := by positivity
  have hb1 : b ≤ 1 := by nlinarith [hab, hb, sq_nonneg a]
  have ha1 : a ≤ 1 := by nlinarith [hab, ha, sq_nonneg b]
  have hq_half : q ≤ 1 / 2 := by nlinarith [hqb, ha, hb, hab]
  have hw1 : 1 ≤ a + b := by nlinarith [hab, ha, hb, sq_nonneg (a - b)]
  have haq : a * q ≤ 1 / 2 := by nlinarith [hqb, hw1, ha1, ha, hq0]
  by_cases hP1 : |b * q - a * u| ≤ 1 / 2 ∧ |b * u + a * q| ≤ 1 / 2
  · exact Or.inl hP1
  · right
    have hB_abs : |b * u + a * q| = b * u + a * q := abs_of_nonneg (by positivity)
    have hAauto : b * q - a * u ≤ 1 / 2 := by
      have h1 : b * q ≤ q := by nlinarith [hb1, hq0]
      have h2 : (0:ℝ) ≤ a * u := by positivity
      linarith
    have hdisj : |b * q - a * u| > 1 / 2 ∨ 1 / 2 < b * u + a * q := by
      rcases not_and_or.mp hP1 with h | h
      · exact Or.inl (not_le.mp h)
      · rw [hB_abs] at h
        exact Or.inr (not_le.mp h)
    have hP2 : b * q + a * (Real.sqrt 2 / 2 - u) ≤ 1 / 2 ∧
        b * (Real.sqrt 2 / 2 - u) - a * q ≤ 1 / 2 := by
      rcases hdisj with h | h
      · have h2 : 1 / 2 < a * u - b * q := by
          rcases lt_abs.mp h with hgt | hlt
          · exfalso
            linarith
          · linarith
        exact l2_case_A a b u q hsp ha hb hab hu0 hur hq0 hqb h2
      · exact l2_case_B a b u q hsp ha hb hab hu0 hur hq0 hqb h
    constructor
    · rw [abs_of_nonneg (by positivity)]
      exact hP2.1
    · rw [abs_le]
      refine ⟨by linarith [hP2.2], ?_⟩
      nlinarith [haq, hb, hur, hr]

private lemma csq_neg (x y a b : ℝ) : csq x y (-a) (-b) = csq x y a b := by
  ext p
  simp only [csq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have e : -a * (p.1 - x) + -b * (p.2 - y) = -(a * (p.1 - x) + b * (p.2 - y)) := by ring
      rw [e, abs_neg] at h1
      exact h1
    · have e : -(-b) * (p.1 - x) + -a * (p.2 - y) = -(-b * (p.1 - x) + a * (p.2 - y)) := by ring
      rw [e, abs_neg] at h2
      exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have e : -a * (p.1 - x) + -b * (p.2 - y) = -(a * (p.1 - x) + b * (p.2 - y)) := by ring
      rw [e, abs_neg]
      exact h1
    · have e : -(-b) * (p.1 - x) + -a * (p.2 - y) = -(-b * (p.1 - x) + a * (p.2 - y)) := by ring
      rw [e, abs_neg]
      exact h2

/-- 正方形集在 frame 旋转 90°：(a,b) ↦ (−b,a) 下不变。 -/
private lemma csq_rot (x y a b : ℝ) : csq x y (-b) a = csq x y a b := by
  ext p
  simp only [csq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have e : -a * (p.1 - x) + -b * (p.2 - y) = -(a * (p.1 - x) + b * (p.2 - y)) := by ring
      rw [e, abs_neg] at h2
      exact h2
    · exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact h2
    · have e : -a * (p.1 - x) + -b * (p.2 - y) = -(a * (p.1 - x) + b * (p.2 - y)) := by ring
      rw [e, abs_neg]
      exact h1

/-- 任意单位 (a,b) 都可归约到 a ≥ 0 且 b ≥ 0 的等价 frame。 -/
private lemma csq_normalize (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ a' b' : ℝ, 0 ≤ a' ∧ 0 ≤ b' ∧ a' ^ 2 + b' ^ 2 = 1 ∧ csq x y a' b' = csq x y a b := by
  rcases le_or_gt 0 a with ha | ha
  · rcases le_or_gt 0 b with hb | hb
    · exact ⟨a, b, ha, hb, hab, rfl⟩
    · exact ⟨-b, a, by linarith, ha, by nlinarith [hab], csq_rot x y a b⟩
  · rcases le_or_gt 0 b with hb | hb
    · have h : csq x y b (-a) = csq x y a b := by
        have h1 : csq x y (-b) a = csq x y a b := csq_rot x y a b
        have h2 : csq x y b (-a) = csq x y (-b) a := by simpa using csq_neg x y (-b) a
        rw [h2, h1]
      exact ⟨b, -a, hb, by linarith, by nlinarith [hab], h⟩
    · exact ⟨-a, -b, by linarith, by linarith, by nlinarith [hab], csq_neg x y a b⟩

/-- 底边条区域的引理 2（Friedman Lemma 2 的 x₀ = √2/2, y₀ = 1 特例）：
中心在 [1, 1+√2/2] × [0,1] 内、且含于 [0,kk]² 的单位闭正方形，必含 (1,1) 或 (1+√2/2,1)。 -/
theorem five_edge_strip_bottom (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hins : csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 1 + Real.sqrt 2 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1, 1) ∈ csq x y a b ∨ (1 + Real.sqrt 2 / 2, 1) ∈ csq x y a b := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hnorm⟩ := csq_normalize x y a b hab
  have hsp : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : (0:ℝ) < Real.sqrt 2 / 2 := by positivity
  have hu0 : 0 ≤ x - 1 := by linarith
  have hu2 : x - 1 ≤ Real.sqrt 2 / 2 := by linarith
  have hq0 : 0 ≤ 1 - y := by linarith
  -- 取 csq 中最低点 (frame 坐标 (−1/2,−1/2)) 得 y ≥ (a₁+b₁)/2
  have hy_low : (a₁ + b₁) / 2 ≤ y := by
    have hP : (x - a₁ / 2 + b₁ / 2, y - b₁ / 2 - a₁ / 2) ∈ csq x y a₁ b₁ := by
      simp only [csq, Set.mem_setOf_eq]
      have hab' : a₁ ^ 2 + b₁ ^ 2 = 1 := hab₁
      constructor
      · have e : a₁ * (x - a₁ / 2 + b₁ / 2 - x) + b₁ * (y - b₁ / 2 - a₁ / 2 - y)
            = -(a₁ ^ 2 + b₁ ^ 2) / 2 := by ring
        rw [e, hab']
        norm_num
      · have e : -b₁ * (x - a₁ / 2 + b₁ / 2 - x) + a₁ * (y - b₁ / 2 - a₁ / 2 - y)
            = -(a₁ ^ 2 + b₁ ^ 2) / 2 := by ring
        rw [e, hab']
        norm_num
    have hP' : (x - a₁ / 2 + b₁ / 2, y - b₁ / 2 - a₁ / 2) ∈ csq x y a b := by
      rw [← hnorm]
      exact hP
    have hmem := hins hP'
    have h2 : 0 ≤ y - b₁ / 2 - a₁ / 2 := hmem.2.1
    linarith
  have hqb : 1 - y ≤ 1 - (a₁ + b₁) / 2 := by linarith
  rcases l2_pos a₁ b₁ (x - 1) (1 - y) hsp ha₁ hb₁ hab₁ hu0 hu2 hq0 hqb with hP1 | hP2
  · left
    rw [← hnorm]
    have e1 : a₁ * (1 - x) + b₁ * (1 - y) = b₁ * (1 - y) - a₁ * (x - 1) := by ring
    have e2 : -b₁ * (1 - x) + a₁ * (1 - y) = b₁ * (x - 1) + a₁ * (1 - y) := by ring
    simp only [csq, Set.mem_setOf_eq, e1, e2]
    exact hP1
  · right
    rw [← hnorm]
    have e1 : a₁ * (1 + Real.sqrt 2 / 2 - x) + b₁ * (1 - y)
        = b₁ * (1 - y) + a₁ * (Real.sqrt 2 / 2 - (x - 1)) := by ring
    have e2 : -b₁ * (1 + Real.sqrt 2 / 2 - x) + a₁ * (1 - y)
        = a₁ * (1 - y) - b₁ * (Real.sqrt 2 / 2 - (x - 1)) := by ring
    simp only [csq, Set.mem_setOf_eq, e1, e2]
    exact hP2

private def osq (x y a b : ℝ) : Set (ℝ × ℝ) :=
  {p | |a * (p.1 - x) + b * (p.2 - y)| < 1 / 2 ∧ |-b * (p.1 - x) + a * (p.2 - y)| < 1 / 2}

private lemma pset_card : pset.card = 4 := by
  have h : (0:ℝ) < Real.sqrt 2 / 2 := by positivity
  simp [pset, h.ne', show (1:ℝ) ≠ 1 + Real.sqrt 2 / 2 by intro hh; linarith]

private lemma coord_bound (A B a b : ℝ) (hA : |A| ≤ 1 / 2) (hB : |B| ≤ 1 / 2) :
    |a * A + (-b) * B| ≤ (|a| + |b|) / 2 := by
  calc |a * A + (-b) * B| ≤ |a * A| + |(-b) * B| := abs_add_le _ _
    _ = |a| * |A| + |b| * |B| := by rw [abs_mul, abs_mul, abs_neg]
    _ ≤ |a| * (1 / 2) + |b| * (1 / 2) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg a))
          (mul_le_mul_of_nonneg_left hB (abs_nonneg b))
    _ = (|a| + |b|) / 2 := by ring

private lemma coord_bound' (A B a b : ℝ) (hA : |A| ≤ 1 / 2) (hB : |B| ≤ 1 / 2) :
    |b * A + a * B| ≤ (|a| + |b|) / 2 := by
  calc |b * A + a * B| ≤ |b * A| + |a * B| := abs_add_le _ _
    _ = |b| * |A| + |a| * |B| := by rw [abs_mul, abs_mul]
    _ ≤ |b| * (1 / 2) + |a| * (1 / 2) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg b))
          (mul_le_mul_of_nonneg_left hB (abs_nonneg a))
    _ = (|a| + |b|) / 2 := by ring

private lemma five_from_unavoidable
    (hunavoid : ∀ x y a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      csq x y a b ⊆ Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk →
      ∃ p ∈ pset, p ∈ csq x y a b)
    (x y a b : Fin 5 → ℝ) (s : ℝ) (hs0 : 0 ≤ s)
    (hbox : ∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2 * x i ∧
      |a i| + |b i| ≤ 2 * (s - x i) ∧ |a i| + |b i| ≤ 2 * y i ∧
      |a i| + |b i| ≤ 2 * (s - y i))
    (hdisj : ∀ i j, i ≠ j → ∀ X Y : ℝ,
      (X, Y) ∈ osq (x i) (y i) (a i) (b i) → ¬ (X, Y) ∈ osq (x j) (y j) (a j) (b j)) :
    kk ≤ s := by
  have hw1 : 1 ≤ |a 0| + |b 0| := by
    have h1 := (hbox 0).1
    have hnn : (0:ℝ) ≤ |a 0| + |b 0| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have h2 : 1 ≤ (|a 0| + |b 0|) ^ 2 := by
      nlinarith [h1, abs_nonneg (a 0), abs_nonneg (b 0), sq_abs (a 0), sq_abs (b 0)]
    nlinarith
  have hs1 : 1 ≤ s := by
    have h1 := (hbox 0).2.1
    have h2 := (hbox 0).2.2.1
    linarith
  by_contra hcon
  have hslt : s < kk := by linarith
  have hspos : 0 < s := by linarith
  set lam := kk / s with hlam
  have hkkpos : (0:ℝ) < kk := by unfold kk; positivity
  have hlampos : 0 < lam := by rw [hlam]; exact div_pos hkkpos hspos
  have hlamgt : 1 < lam := by rw [hlam, lt_div_iff₀ hspos]; linarith
  have hlams : lam * s = kk := by rw [hlam]; field_simp
  have hwin : ∀ i, csq (lam * x i) (lam * y i) (a i) (b i) ⊆
      Set.Icc (0:ℝ) kk ×ˢ Set.Icc (0:ℝ) kk := by
    intro i p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hhab := (hbox i).1
    have h1a : |a i| + |b i| ≤ 2 * x i := (hbox i).2.1
    have h1b : |a i| + |b i| ≤ 2 * (s - x i) := (hbox i).2.2.1
    have h1c : |a i| + |b i| ≤ 2 * y i := (hbox i).2.2.2.1
    have h1d : |a i| + |b i| ≤ 2 * (s - y i) := (hbox i).2.2.2.2
    set A := a i * (p.1 - lam * x i) + b i * (p.2 - lam * y i) with hA
    set B := (-b i) * (p.1 - lam * x i) + a i * (p.2 - lam * y i) with hB
    have hXb : |p.1 - lam * x i| ≤ (|a i| + |b i|) / 2 := by
      have he : p.1 - lam * x i = a i * A + (-b i) * B := by
        have h2 : a i * A + (-b i) * B = (a i ^ 2 + b i ^ 2) * (p.1 - lam * x i) := by
          rw [hA, hB]; ring
        rw [h2, hhab, one_mul]
      rw [he]
      exact coord_bound A B (a i) (b i) hp1 hp2
    have hYb : |p.2 - lam * y i| ≤ (|a i| + |b i|) / 2 := by
      have he : p.2 - lam * y i = b i * A + a i * B := by
        have h2 : b i * A + a i * B = (a i ^ 2 + b i ^ 2) * (p.2 - lam * y i) := by
          rw [hA, hB]; ring
        rw [h2, hhab, one_mul]
      rw [he]
      exact coord_bound' A B (a i) (b i) hp1 hp2
    have hX' := abs_le.mp hXb
    have hY' := abs_le.mp hYb
    have hw2 : (0:ℝ) ≤ |a i| + |b i| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hlx1 : lam * ((|a i| + |b i|) / 2) ≤ lam * x i := by
      have h2 : (|a i| + |b i|) / 2 ≤ x i := by linarith
      exact mul_le_mul_of_nonneg_left h2 hlampos.le
    have hlx2 : lam * x i + lam * ((|a i| + |b i|) / 2) ≤ kk := by
      have h2 : x i + (|a i| + |b i|) / 2 ≤ s := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hlampos.le
      nlinarith [h3, hlams]
    have hly1 : lam * ((|a i| + |b i|) / 2) ≤ lam * y i := by
      have h2 : (|a i| + |b i|) / 2 ≤ y i := by linarith
      exact mul_le_mul_of_nonneg_left h2 hlampos.le
    have hly2 : lam * y i + lam * ((|a i| + |b i|) / 2) ≤ kk := by
      have h2 : y i + (|a i| + |b i|) / 2 ≤ s := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hlampos.le
      nlinarith [h3, hlams]
    have hwpos : (0:ℝ) ≤ (|a i| + |b i|) / 2 := by
      have := add_nonneg (abs_nonneg (a i)) (abs_nonneg (b i))
      linarith
    have hlamw : 0 ≤ (lam - 1) * ((|a i| + |b i|) / 2) := mul_nonneg (by linarith) hwpos
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      linarith [hX'.1, hX'.2, hY'.1, hY'.2, hlx1, hlx2, hly1, hly2, hlamw]
  have hex : ∀ i, ∃ p ∈ pset, p ∈ csq (lam * x i) (lam * y i) (a i) (b i) :=
    fun i => hunavoid (lam * x i) (lam * y i) (a i) (b i) (hbox i).1 (hwin i)
  choose pp hpp hpm using hex
  have hint : ∀ i, ((pp i).1 / lam, (pp i).2 / lam) ∈ osq (x i) (y i) (a i) (b i) := by
    intro i
    obtain ⟨h1, h2⟩ := hpm i
    have hdivlt : (1:ℝ) / 2 / lam < 1 / 2 := by rw [div_lt_iff₀ hlampos]; nlinarith
    constructor
    · have he : a i * ((pp i).1 / lam - x i) + b i * ((pp i).2 / lam - y i)
          = (a i * ((pp i).1 - lam * x i) + b i * ((pp i).2 - lam * y i)) / lam := by
        field_simp
      rw [he, abs_div, abs_of_pos hlampos]
      have hle : |a i * ((pp i).1 - lam * x i) + b i * ((pp i).2 - lam * y i)| / lam ≤
          (1 / 2) / lam := by gcongr
      linarith
    · have he : (-b i) * ((pp i).1 / lam - x i) + a i * ((pp i).2 / lam - y i)
          = ((-b i) * ((pp i).1 - lam * x i) + a i * ((pp i).2 - lam * y i)) / lam := by
        field_simp
      rw [he, abs_div, abs_of_pos hlampos]
      have hle : |(-b i) * ((pp i).1 - lam * x i) + a i * ((pp i).2 - lam * y i)| / lam ≤
          (1 / 2) / lam := by gcongr
      linarith
  have hinj : Function.Injective pp := by
    intro i j hij
    by_contra hne
    have hq1 := hint i
    have hq2 : ((pp i).1 / lam, (pp i).2 / lam) ∈ osq (x j) (y j) (a j) (b j) := by
      rw [hij]
      exact hint j
    exact hdisj i j hne ((pp i).1 / lam) ((pp i).2 / lam) hq1 hq2
  have hcard : 5 ≤ pset.card := by
    have hinj' : Function.Injective (fun i : Fin 5 => (⟨pp i, hpp i⟩ : ↥pset)) := by
      intro i j hij
      exact hinj (congrArg Subtype.val hij)
    have h := Fintype.card_le_of_injective (fun i : Fin 5 => (⟨pp i, hpp i⟩ : ↥pset)) hinj'
    simpa [Fintype.card_coe] using h
  rw [pset_card] at hcard
  omega

theorem PEqualNP.Outside.L_square_packing_five_optimality :
    let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; let fits := fun (n : ℕ) (s : ℝ) => 0 ≤ s ∧ ∃ x y a b : Fin n → ℝ, (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2*x i ∧ |a i| + |b i| ≤ 2*(s-x i) ∧ |a i| + |b i| ≤ 2*y i ∧ |a i| + |b i| ≤ 2*(s-y i)) ∧ (∀ i j, i ≠ j → ∀ X Y : ℝ, inside (x i) (y i) (a i) (b i) X Y → ¬ inside (x j) (y j) (a j) (b j) X Y); ∀ s : ℝ, fits 5 s → 2 + Real.sqrt 2 / 2 ≤ s := by
  change ∀ (s : ℝ), 0 ≤ s ∧
      (∃ x y a b : Fin 5 → ℝ,
        (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2 * x i ∧
          |a i| + |b i| ≤ 2 * (s - x i) ∧ |a i| + |b i| ≤ 2 * y i ∧
          |a i| + |b i| ≤ 2 * (s - y i)) ∧
        (∀ i j, i ≠ j → ∀ X Y : ℝ,
          (|a i * (X - x i) + b i * (Y - y i)| < 1 / 2 ∧
            |(-b i) * (X - x i) + a i * (Y - y i)| < 1 / 2) →
          ¬(|a j * (X - x j) + b j * (Y - y j)| < 1 / 2 ∧
            |(-b j) * (X - x j) + a j * (Y - y j)| < 1 / 2))) → kk ≤ s
  intro s hfits
  obtain ⟨hs0, x, y, a, b, hbox, hdisj⟩ := hfits
  exact five_from_unavoidable (five_unavoidable five_edge_strip_bottom) x y a b s hs0 hbox hdisj
