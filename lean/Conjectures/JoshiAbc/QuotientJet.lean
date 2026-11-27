import Mathlib

private lemma real_pow_le_pow_of_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {m n : ℕ} (hmn : m ≤ n) : a ^ n ≤ a ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (pow_le_one₀ ha0 ha1 : a ^ k ≤ 1) (pow_nonneg ha0 m)

private lemma fourteen_mul_tri_div_two (n : ℤ) :
    (14 : ℤ) * (n * (n + 1) / 2) = 7 * (n * (n + 1)) := by
  obtain ⟨q, h | h⟩ : ∃ q : ℤ, n = 2 * q ∨ n = 2 * q + 1 := ⟨n / 2, by omega⟩
  · subst h
    have h1 : (2 * q) * (2 * q + 1) = 2 * (q * (2 * q + 1)) := by ring
    rw [h1]
    omega
  · subst h
    have h1 : (2 * q + 1) * (2 * q + 1 + 1) = 2 * ((2 * q + 1) * (q + 1)) := by ring
    rw [h1]
    omega

private lemma ultra_norm_add_le {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K]
    (x y : K) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [dist_eq_norm] using IsUltrametricDist.dist_triangle_max (x + y) y 0

private lemma ultra_norm_sub_le {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K]
    (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [dist_eq_norm] using IsUltrametricDist.dist_triangle_max x 0 y

private lemma ultra_norm_add_eq_left {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K]
    {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  apply le_antisymm
  · exact (ultra_norm_add_le x y).trans (max_le le_rfl h.le)
  · have h1 : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
      simpa [add_sub_cancel_right] using ultra_norm_sub_le (x + y) y
    rcases le_max_iff.mp h1 with hle | hle
    · exact hle
    · exact absurd hle (not_le_of_gt h)

private lemma ultra_norm_sum_range_le {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K]
    (f : ℕ → K) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f n‖ ≤ C := by
  induction N with
  | zero => simpa using hC
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact (ultra_norm_add_le _ _).trans (max_le ih (hf N))

private lemma ultra_norm_tsum_nat_le {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K]
    {f : ℕ → K} (hf_sum : Summable f) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) :
    ‖∑' n : ℕ, f n‖ ≤ C := by
  have htend : Filter.Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.range N, f n‖)
      Filter.atTop (nhds ‖∑' n : ℕ, f n‖) :=
    (continuous_norm.tendsto _).comp hf_sum.tendsto_sum_tsum_nat
  exact le_of_tendsto' htend (fun N => ultra_norm_sum_range_le f C hC hf N)

private lemma norm_theta_term {K : Type} [NontriviallyNormedField K]
    {r u : K} (hr_pos : 0 < ‖r‖) {c : ℕ} (hu : ‖u‖ = ‖r‖ ^ c) (n : ℤ) :
    ‖(r ^ 14) ^ (n * (n + 1) / 2) * u ^ (2 * n + 1)‖ =
      ‖r‖ ^ (7 * (n * (n + 1)) + (c : ℤ) * (2 * n + 1)) := by
  have hr0 : ‖r‖ ≠ 0 := ne_of_gt hr_pos
  rw [norm_mul, norm_zpow, norm_pow, norm_zpow, hu]
  rw [← zpow_natCast ‖r‖ 14, ← zpow_natCast ‖r‖ c]
  rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hr0]
  congr 1
  simp only [Nat.cast_ofNat]
  rw [fourteen_mul_tri_div_two]

theorem Conjectures.JoshiAbc.QuotientJet :
  ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ (r z : K), r^14=(29:K) → 0 < ‖r‖ → ‖r‖ < 1 → z^7=1 → ‖z‖=1 → ‖1+z^2‖=1 → ‖theta (r^14) (r*z) / theta (r^14) (r^2*z) - (r+z^2*r^3)‖ ≤ ‖r‖^4 := by
  intro K _ _ _ _ theta r z _ hr_pos hr_lt _ hz_norm _
  let a : ℤ → K := fun n => (r ^ 14) ^ (n * (n + 1) / 2) * (r * z) ^ (2 * n + 1)
  let b : ℤ → K := fun n => (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1)
  change ‖(∑' n : ℤ, a n) / (∑' n : ℤ, b n) - (r + z ^ 2 * r ^ 3)‖ ≤ ‖r‖ ^ 4
  have hr_ne : r ≠ 0 := by
    intro h
    rw [h, norm_zero] at hr_pos
    exact lt_irrefl 0 hr_pos
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz_norm
    norm_num at hz_norm
  have hu1 : ‖r * z‖ = ‖r‖ ^ 1 := by
    rw [norm_mul, hz_norm, mul_one, pow_one]
  have hu2 : ‖r ^ 2 * z‖ = ‖r‖ ^ 2 := by
    rw [norm_mul, norm_pow, hz_norm, mul_one]
  have ha_pos_tail_norm : ∀ k : ℕ, ‖a ((k + 1 : ℕ) : ℤ)‖ = ‖r‖ ^ (7 * k * k + 23 * k + 17) := by
    intro k
    rw [norm_theta_term hr_pos hu1]
    have hexp : 7 * (((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) + 1)) +
        ((1 : ℕ) : ℤ) * (2 * ((k + 1 : ℕ) : ℤ) + 1) =
        ((7 * k * k + 23 * k + 17 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hexp, zpow_natCast]
  have ha_neg_tail_norm : ∀ k : ℕ,
      ‖a (-(((k + 1 : ℕ) : ℤ) + 1))‖ = ‖r‖ ^ (7 * k * k + 19 * k + 11) := by
    intro k
    rw [norm_theta_term hr_pos hu1]
    have hexp : 7 * ((-(((k + 1 : ℕ) : ℤ) + 1)) * (-(((k + 1 : ℕ) : ℤ) + 1) + 1)) +
        ((1 : ℕ) : ℤ) * (2 * (-(((k + 1 : ℕ) : ℤ) + 1)) + 1) =
        ((7 * k * k + 19 * k + 11 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hexp, zpow_natCast]
  have hb_pos_norm : ∀ k : ℕ, ‖b (k : ℤ)‖ = ‖r‖ ^ (7 * k * k + 11 * k + 2) := by
    intro k
    rw [norm_theta_term hr_pos hu2]
    have hexp : 7 * ((k : ℤ) * ((k : ℤ) + 1)) +
        ((2 : ℕ) : ℤ) * (2 * (k : ℤ) + 1) =
        ((7 * k * k + 11 * k + 2 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hexp, zpow_natCast]
  have hb_neg_tail_norm : ∀ k : ℕ,
      ‖b (-(((k + 1 : ℕ) : ℤ) + 1))‖ = ‖r‖ ^ (7 * k * k + 17 * k + 8) := by
    intro k
    rw [norm_theta_term hr_pos hu2]
    have hexp : 7 * ((-(((k + 1 : ℕ) : ℤ) + 1)) * (-(((k + 1 : ℕ) : ℤ) + 1) + 1)) +
        ((2 : ℕ) : ℤ) * (2 * (-(((k + 1 : ℕ) : ℤ) + 1)) + 1) =
        ((7 * k * k + 17 * k + 8 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hexp, zpow_natCast]
  have hgeom : Summable (fun k : ℕ => ‖r‖ ^ k) :=
    summable_geometric_of_lt_one hr_pos.le hr_lt
  have ha_pos_tail_sum : Summable (fun k : ℕ => a ((k + 1 : ℕ) : ℤ)) :=
    Summable.of_norm_bounded hgeom (fun k => by
      rw [ha_pos_tail_norm]
      exact real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega))
  have ha_pos_sum : Summable (fun k : ℕ => a (k : ℤ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => a (k : ℤ)) 1).mp ha_pos_tail_sum
  have ha_neg_tail_sum : Summable (fun k : ℕ => a (-(((k + 1 : ℕ) : ℤ) + 1))) :=
    Summable.of_norm_bounded hgeom (fun k => by
      rw [ha_neg_tail_norm]
      exact real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega))
  have ha_neg_sum : Summable (fun k : ℕ => a (-((k : ℤ) + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => a (-((k : ℤ) + 1))) 1).mp ha_neg_tail_sum
  have hb_pos_sum : Summable (fun k : ℕ => b (k : ℤ)) :=
    Summable.of_norm_bounded hgeom (fun k => by
      rw [hb_pos_norm]
      exact real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega))
  have hb_neg_tail_sum : Summable (fun k : ℕ => b (-(((k + 1 : ℕ) : ℤ) + 1))) :=
    Summable.of_norm_bounded hgeom (fun k => by
      rw [hb_neg_tail_norm]
      exact real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega))
  have hb_neg_sum : Summable (fun k : ℕ => b (-((k : ℤ) + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => b (-((k : ℤ) + 1))) 1).mp hb_neg_tail_sum
  let RN_pos : K := ∑' k : ℕ, a ((k + 1 : ℕ) : ℤ)
  let RN_neg : K := ∑' k : ℕ, a (-(((k + 1 : ℕ) : ℤ) + 1))
  let RN : K := RN_pos + RN_neg
  have hN_eq : (∑' n : ℤ, a n) = a (-1) + a 0 + RN := by
    rw [tsum_of_nat_of_neg_add_one ha_pos_sum ha_neg_sum]
    rw [ha_pos_sum.tsum_eq_zero_add, ha_neg_sum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_add]
    dsimp only [RN, RN_pos, RN_neg]
    ring
  let SD_pos : K := ∑' k : ℕ, b (k : ℤ)
  let SD_neg : K := ∑' k : ℕ, b (-(((k + 1 : ℕ) : ℤ) + 1))
  let SD : K := SD_pos + SD_neg
  have hD_eq : (∑' n : ℤ, b n) = b (-1) + SD := by
    rw [tsum_of_nat_of_neg_add_one hb_pos_sum hb_neg_sum]
    rw [hb_neg_sum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_add]
    dsimp only [SD, SD_pos, SD_neg]
    ring
  have hRN_pos_norm : ‖RN_pos‖ ≤ ‖r‖ ^ 3 :=
    ultra_norm_tsum_nat_le ha_pos_tail_sum (pow_nonneg hr_pos.le 3) (fun k => by
      rw [ha_pos_tail_norm]
      exact real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega))
  have hRN_neg_norm : ‖RN_neg‖ ≤ ‖r‖ ^ 3 :=
    ultra_norm_tsum_nat_le ha_neg_tail_sum (pow_nonneg hr_pos.le 3) (fun k => by
      rw [ha_neg_tail_norm]
      exact real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega))
  have hRN_norm : ‖RN‖ ≤ ‖r‖ ^ 3 :=
    (ultra_norm_add_le RN_pos RN_neg).trans (max_le hRN_pos_norm hRN_neg_norm)
  have hSD_pos_norm : ‖SD_pos‖ ≤ ‖r‖ ^ 2 :=
    ultra_norm_tsum_nat_le hb_pos_sum (pow_nonneg hr_pos.le 2) (fun k => by
      rw [hb_pos_norm]
      exact real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega))
  have hSD_neg_norm : ‖SD_neg‖ ≤ ‖r‖ ^ 2 :=
    ultra_norm_tsum_nat_le hb_neg_tail_sum (pow_nonneg hr_pos.le 2) (fun k => by
      rw [hb_neg_tail_norm]
      exact real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega))
  have hSD_norm : ‖SD‖ ≤ ‖r‖ ^ 2 :=
    (ultra_norm_add_le SD_pos SD_neg).trans (max_le hSD_pos_norm hSD_neg_norm)
  have ha0 : a 0 = r * z := by
    simp [a]
  have ha_neg1 : a (-1) = r⁻¹ * z⁻¹ := by
    dsimp [a]
    simp [mul_inv_rev, mul_comm]
  have hb_neg1 : b (-1) = (r ^ 2)⁻¹ * z⁻¹ := by
    dsimp [b]
    simp [mul_inv_rev, mul_comm]
  have hb_neg1_norm : ‖b (-1)‖ = (‖r‖ ^ 2)⁻¹ := by
    rw [hb_neg1, norm_mul, norm_inv, norm_pow, norm_inv, hz_norm, inv_one, mul_one]
  have hr2_pos : 0 < ‖r‖ ^ 2 := pow_pos hr_pos 2
  have hr2_lt_one : ‖r‖ ^ 2 < 1 := by nlinarith
  have hr2_lt_inv : ‖r‖ ^ 2 < (‖r‖ ^ 2)⁻¹ := by
    have hmul : (‖r‖ ^ 2) * (‖r‖ ^ 2) < 1 := by nlinarith
    have h1 : (‖r‖ ^ 2) * (‖r‖ ^ 2) < (‖r‖ ^ 2) * (‖r‖ ^ 2)⁻¹ := by
      rwa [mul_inv_cancel₀ (ne_of_gt hr2_pos)]
    exact lt_of_mul_lt_mul_left h1 hr2_pos.le
  have hSD_lt : ‖SD‖ < ‖b (-1)‖ := by
    rw [hb_neg1_norm]
    exact lt_of_le_of_lt hSD_norm hr2_lt_inv
  have hD_norm : ‖∑' n : ℤ, b n‖ = (‖r‖ ^ 2)⁻¹ := by
    rw [hD_eq, ultra_norm_add_eq_left hSD_lt, hb_neg1_norm]
  have hD_ne : (∑' n : ℤ, b n) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hD_norm
    have hinv_pos : (0 : ℝ) < (‖r‖ ^ 2)⁻¹ := inv_pos.mpr hr2_pos
    linarith
  have hcancel : (r + z ^ 2 * r ^ 3) * b (-1) = a (-1) + a 0 := by
    rw [hb_neg1, ha_neg1, ha0]
    have hrz : r ^ 2 * z ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr_ne) hz_ne
    apply mul_right_cancel₀ hrz
    calc
      (r + z ^ 2 * r ^ 3) * ((r ^ 2)⁻¹ * z⁻¹) * (r ^ 2 * z)
          = (r + z ^ 2 * r ^ 3) * ((r ^ 2)⁻¹ * r ^ 2) * (z⁻¹ * z) := by ring
      _ = r + z ^ 2 * r ^ 3 := by
            rw [inv_mul_cancel₀ (pow_ne_zero 2 hr_ne), inv_mul_cancel₀ hz_ne]
            ring
      _ = (r⁻¹ * r) * (z⁻¹ * z) * r + r * z * (r ^ 2 * z) := by
            rw [inv_mul_cancel₀ hr_ne, inv_mul_cancel₀ hz_ne]
            ring
      _ = (r⁻¹ * z⁻¹ + r * z) * (r ^ 2 * z) := by ring
  have hnum : (∑' n : ℤ, a n) - (r + z ^ 2 * r ^ 3) * (∑' n : ℤ, b n) =
      RN - (r + z ^ 2 * r ^ 3) * SD := by
    rw [hN_eq, hD_eq, mul_add, hcancel]
    ring
  have hcoeff : ‖r + z ^ 2 * r ^ 3‖ ≤ ‖r‖ := by
    refine (ultra_norm_add_le r (z ^ 2 * r ^ 3)).trans (max_le le_rfl ?_)
    rw [norm_mul, norm_pow, hz_norm, one_pow, one_mul, norm_pow]
    simpa using real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega : 1 ≤ 3)
  have hterm2 : ‖(r + z ^ 2 * r ^ 3) * SD‖ ≤ ‖r‖ ^ 3 := by
    rw [norm_mul]
    calc
      ‖r + z ^ 2 * r ^ 3‖ * ‖SD‖ ≤ ‖r‖ * ‖r‖ ^ 2 :=
        mul_le_mul hcoeff hSD_norm (norm_nonneg _) hr_pos.le
      _ = ‖r‖ ^ 3 := by ring
  have hnum_norm : ‖(∑' n : ℤ, a n) - (r + z ^ 2 * r ^ 3) * (∑' n : ℤ, b n)‖ ≤ ‖r‖ ^ 3 := by
    rw [hnum]
    exact (ultra_norm_sub_le _ _).trans (max_le hRN_norm hterm2)
  have hdiv : (∑' n : ℤ, a n) / (∑' n : ℤ, b n) - (r + z ^ 2 * r ^ 3) =
      ((∑' n : ℤ, a n) - (r + z ^ 2 * r ^ 3) * (∑' n : ℤ, b n)) / (∑' n : ℤ, b n) := by
    rw [sub_div, mul_div_cancel_right₀ _ hD_ne]
  rw [hdiv, norm_div, hD_norm, div_inv_eq_mul]
  calc
    ‖(∑' n : ℤ, a n) - (r + z ^ 2 * r ^ 3) * (∑' n : ℤ, b n)‖ * ‖r‖ ^ 2
        ≤ ‖r‖ ^ 3 * ‖r‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hnum_norm (pow_nonneg hr_pos.le 2)
    _ = ‖r‖ ^ 5 := by ring
    _ ≤ ‖r‖ ^ 4 := real_pow_le_pow_of_le_one hr_pos.le hr_lt.le (by omega)
