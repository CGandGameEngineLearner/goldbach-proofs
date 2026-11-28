import Mathlib
import Conjectures.Goldbach.FareyLateFirstHitFactorSwitch
import Conjectures.Goldbach.FareyLatePrimeSquareLoss

/-- The reciprocal as a monoid hom. -/
noncomputable def refute6808_L1_inv : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by simp [mul_comm]

lemma refute6808_L1_euler (y : ℕ) :
    Real.log y ≤ ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := refute6808_L1_inv) (N := y + 1) (by
      intro p hp
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      show ‖(p : ℝ)⁻¹‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_lt_one_of_one_lt₀ this)).2
  have hfin : ∑ m ∈ (Finset.Icc 1 y).subtype (fun m => m ∈ (y + 1).smoothNumbers),
      refute6808_L1_inv (m : ℕ) ≤ ∏ p ∈ (y + 1).primesBelow, (1 - refute6808_L1_inv p)⁻¹ := by
    apply sum_le_hasSum _ _ h
    intro i _
    show 0 ≤ (i.1 : ℝ)⁻¹
    positivity
  have hsub : (Finset.Icc 1 y).subtype (fun m => m ∈ (y + 1).smoothNumbers)
      = (Finset.Icc 1 y).subtype (fun m => m ∈ (y + 1).smoothNumbers) := rfl
  have hsum : ∑ m ∈ (Finset.Icc 1 y).subtype (fun m => m ∈ (y + 1).smoothNumbers),
      refute6808_L1_inv (m : ℕ) = ∑ m ∈ Finset.Icc 1 y, ((m : ℕ) : ℝ)⁻¹ := by
    refine Finset.sum_subtype_of_mem (fun m : ℕ => ((m : ℕ) : ℝ)⁻¹) ?_
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Nat.mem_smoothNumbers']
    intro p hp hpd
    have := Nat.le_of_dvd (by omega) hpd
    omega
  have hh : Real.log y ≤ ∑ m ∈ Finset.Icc 1 y, ((m : ℕ) : ℝ)⁻¹ := by
    have h1 := log_le_harmonic_floor (y : ℝ) (by positivity)
    rw [Nat.floor_natCast, harmonic_eq_sum_Icc] at h1
    simpa using h1
  have : ∑ m ∈ (Finset.Icc 1 y).subtype (fun m => m ∈ (y + 1).smoothNumbers),
      refute6808_L1_inv (m : ℕ) = ∑ m ∈ Finset.Icc 1 y, ((m : ℕ) : ℝ)⁻¹ := hsum
  have hp : ∏ p ∈ (y + 1).primesBelow, (1 - refute6808_L1_inv p)⁻¹
      = ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := rfl
  linarith

theorem refute6808_L1 : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
    ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 3 y), (1 - 2 / (p : ℝ)) ≤ C / (Real.log y) ^ 2 := by
  refine ⟨4, by norm_num, fun y hy => ?_⟩
  have hS : (y + 1).primesBelow = insert 2 (Finset.filter Nat.Prime (Finset.Icc 3 y)) := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : p = 2
      · exact Or.inl h
      · right; exact ⟨⟨by have := h2.two_le; omega, by omega⟩, h2⟩
    · rintro (h | ⟨⟨h1, h2⟩, h3⟩)
      · subst h; exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨by omega, h3⟩
  have h2 : (2 : ℕ) ∉ Finset.filter Nat.Prime (Finset.Icc 3 y) := by simp
  set T := Finset.filter Nat.Prime (Finset.Icc 3 y) with hT
  have hE := refute6808_L1_euler y
  rw [hS, Finset.prod_insert h2] at hE
  have hlog : 0 < Real.log y := Real.log_pos (by exact_mod_cast hy)
  have hpos : ∀ p ∈ T, 0 < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      exact_mod_cast this
    have : (p : ℝ)⁻¹ ≤ 1 / 3 := by
      rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hp3
    linarith
  set Q := ∏ p ∈ T, (1 - (p : ℝ)⁻¹) with hQ
  have hQpos : 0 < Q := Finset.prod_pos hpos
  have hQle : ∏ p ∈ T, (1 - 2 / (p : ℝ)) ≤ Q ^ 2 := by
    rw [hQ, sq, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · 
      have hp3 : (3 : ℝ) ≤ p := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        exact_mod_cast this
      have : 2 / (p : ℝ) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
      linarith
    · 
      have hp0 : (0 : ℝ) < p := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        have : (0 : ℕ) < p := by omega
        exact_mod_cast this
      have : 2 / (p : ℝ) = 2 * (p : ℝ)⁻¹ := by ring
      rw [this]
      nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  have hE' : Real.log y ≤ (1 - ((2 : ℕ) : ℝ)⁻¹)⁻¹ * Q⁻¹ := by
    rw [hQ, ← Finset.prod_inv_distrib]; exact hE
  have hval : (1 - ((2 : ℕ) : ℝ)⁻¹)⁻¹ = 2 := by norm_num
  rw [hval] at hE'
  have hQ4 : Q ≤ 2 / Real.log y := by
    rw [le_div_iff₀ hlog]
    have : Real.log y * Q ≤ 2 := by
      calc Real.log y * Q ≤ (2 * Q⁻¹) * Q := mul_le_mul_of_nonneg_right hE' hQpos.le
        _ = 2 := by field_simp
    linarith
  calc ∏ p ∈ T, (1 - 2 / (p : ℝ)) ≤ Q ^ 2 := hQle
    _ ≤ (2 / Real.log y) ^ 2 := by gcongr
    _ = 4 / Real.log y ^ 2 := by ring

open Nat in
/-- Adapted from the Mathlib Bertrand proof, without the no-prime hypothesis. -/
theorem refute6808_L2_cb (n : ℕ) (hn : 2 < n) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ (((Finset.Ioc n (2 * n)).filter Nat.Prime).card) := by
  have n_pos : 0 < n := by omega
  have n2_pos : 1 ≤ 2 * n := by omega
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  let S1 := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let S2 := {p ∈ Finset.Ioc (2 * n / 3) (2 * n) | Nat.Prime p}
  have h1 : ∏ x ∈ Finset.range (2 * n + 1), f x
      = ∏ x ∈ (Finset.range (2 * n + 1)).filter Nat.Prime, f x := by
    refine (Finset.prod_filter_of_ne fun p _ h => ?_).symm
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, Nat.pow_zero]
  have hset : (Finset.range (2 * n + 1)).filter Nat.Prime = S1 ∪ S2 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Ioc, S1, S2]
    constructor
    · rintro ⟨h, hp⟩
      by_cases c : p ≤ 2 * n / 3
      · left; exact ⟨by omega, hp⟩
      · right; exact ⟨⟨by omega, by omega⟩, hp⟩
    · rintro (⟨h, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
      · exact ⟨by omega, hp⟩
      · exact ⟨by omega, hp⟩
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, S1, S2] at hp1 hp2
    omega
  have hsplit : centralBinom n = (∏ x ∈ S1, f x) * ∏ x ∈ S2, f x := by
    rw [← Finset.prod_union hdisj, ← hset, ← h1]
    exact (Nat.prod_pow_factorization_centralBinom n).symm
  rw [hsplit]
  apply mul_le_mul'
  · rw [← Finset.prod_filter_mul_prod_filter_not S1 (· ≤ sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
      have : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by
        rw [card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · rw [← Finset.prod_filter_mul_prod_filter_not S2 (fun p => n < p)]
    have hone : ∏ x ∈ S2.filter (fun p => ¬ n < p), f x = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc, S2] at hp
      obtain ⟨⟨⟨h1, h2⟩, hpp⟩, h3⟩ := hp
      show p ^ _ = 1
      rw [factorization_centralBinom_of_two_mul_self_lt_three_mul hn (by omega) (by omega),
        Nat.pow_zero]
    rw [hone, mul_one]
    refine (Finset.prod_le_prod (fun p _ => (?_ : f p ≤ 2 * n))).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos (Finset.card_le_card ?_)
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc, S2] at hp ⊢
    obtain ⟨⟨⟨h1, h2⟩, hpp⟩, h3⟩ := hp
    exact ⟨⟨h3, h2⟩, hpp⟩

theorem refute6808_L2 : ∃ c : ℝ, 0 < c ∧ ∃ y0 : ℕ, ∀ y : ℕ, y0 ≤ y →
    c * (y : ℝ) / Real.log y ≤ (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ) := by
  refine ⟨1 / 10, by norm_num, 15000000, ?_⟩
  intro y hy
  set P : ℕ := ((Finset.Ioc y (2 * y)).filter Nat.Prime).card with hP
  have hy4 : 4 ≤ y := by omega
  have hY : (15000000 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlt0 := Nat.four_pow_lt_mul_centralBinom y hy4
  have hcb := refute6808_L2_cb y (by omega)
  have hlt : 4 ^ y < y * ((2 * y) ^ Nat.sqrt (2 * y) * 4 ^ (2 * y / 3) * (2 * y) ^ P) :=
    lt_of_lt_of_le hlt0 (Nat.mul_le_mul_left y hcb)
  have hltR : (4 : ℝ) ^ y < (y : ℝ) * (((2 : ℝ) * y) ^ Nat.sqrt (2 * y) * 4 ^ (2 * y / 3) *
      ((2 : ℝ) * y) ^ P) := by exact_mod_cast hlt
  have hYpos : (0 : ℝ) < y := by linarith
  have h2Y : (0 : ℝ) < 2 * y := by linarith
  set L : ℝ := Real.log (2 * y) with hL
  set s : ℕ := Nat.sqrt (2 * y) with hs
  have hlog := Real.log_lt_log (by positivity) hltR
  rw [Real.log_mul hYpos.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  rw [← hL] at hlog
  -- constants
  set l : ℝ := Real.log 4 with hl
  have hl2 : (1.38 : ℝ) ≤ l := by
    have : l = 2 * Real.log 2 := by
      rw [hl, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  -- the fourth root
  set u : ℝ := ((2 : ℝ) * y) ^ (1 / 4 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos h2Y _
  have hu4 : u ^ 4 = 2 * y := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul h2Y.le]; norm_num
  have hu73 : (73 : ℝ) ≤ u := by
    by_contra hcon
    push_neg at hcon
    have : u ^ 4 < 73 ^ 4 := pow_lt_pow_left₀ hcon hu0.le (by norm_num)
    nlinarith
  have hsq : Real.sqrt (2 * y) = u ^ 2 := by
    rw [show (2 : ℝ) * y = (u ^ 2) ^ 2 by rw [← pow_mul]; exact hu4.symm]
    exact Real.sqrt_sq (by positivity)
  have hs_le : (s : ℝ) ≤ u ^ 2 := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * y)
    rw [← hs] at this
    push_cast at this
    linarith
  have hLle : L ≤ 4 * u := by
    have := Real.log_le_rpow_div h2Y.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [← hL, ← hu] at this
    linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hlogY : Real.log y ≤ L := Real.log_le_log hYpos (by linarith)
  have hT : ((2 * y / 3 : ℕ) : ℝ) ≤ 2 * y / 3 := by
    have := Nat.cast_div_le (α := ℝ) (m := 2 * y) (n := 3)
    push_cast at this
    linarith
  have hSL : (s : ℝ) * L ≤ u ^ 2 * (4 * u) :=
    mul_le_mul hs_le hLle hLpos.le (by positivity)
  have hTl : ((2 * y / 3 : ℕ) : ℝ) * l ≤ (2 * y / 3) * l :=
    mul_le_mul_of_nonneg_right hT (by linarith)
  have hPL : (y : ℝ) * l / 6 ≤ (P : ℝ) * L := by
    have hY' : (y : ℝ) = u ^ 4 / 2 := by linarith
    have hu3 : u ≤ u ^ 3 := by nlinarith [mul_pos hu0 hu0]
    have h8 : 8 * u ^ 3 ≤ u ^ 4 * 1.38 / 12 := by
      have : (73 : ℝ) * u ^ 3 ≤ u ^ 4 := by
        have : u ^ 4 = u * u ^ 3 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hu73 (by positivity)
      nlinarith [pow_pos hu0 3]
    have hYl : u ^ 4 * 1.38 / 12 ≤ (y : ℝ) * l / 3 - (y : ℝ) * l / 6 := by
      rw [hY']
      nlinarith [pow_pos hu0 4]
    nlinarith
  have hlogYpos : 0 < Real.log y := Real.log_pos (by linarith)
  have hL2 : L ≤ 2 * Real.log y := by
    have : L = Real.log 2 + Real.log y := by
      rw [hL, Real.log_mul (by norm_num) hYpos.ne']
    have h2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
    linarith
  rw [div_le_iff₀ hlogYpos]
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have : (P : ℝ) * L ≤ (P : ℝ) * (2 * Real.log y) := mul_le_mul_of_nonneg_left hL2 hP0
  nlinarith

theorem refute6808_L3_minFac {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p < q) :
    (p * q).minFac = p := by
  have hne : p * q ≠ 1 := by
    intro h1
    have := hp.two_le
    have := hq.two_le
    nlinarith
  have hmp : (p * q).minFac.Prime := Nat.minFac_prime hne
  have hd : (p * q).minFac ∣ p * q := Nat.minFac_dvd _
  have hle : (p * q).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases (Nat.Prime.dvd_mul hmp).1 hd with h1 | h1
  · exact (Nat.prime_dvd_prime_iff_eq hmp hp).1 h1
  · have := (Nat.prime_dvd_prime_iff_eq hmp hq).1 h1
    omega

theorem refute6808_L3_pair (n p q : ℕ) (hp : p.Prime) (h3 : 3 * p * p ≤ n)
    (hq : q ∈ (Finset.Ioc (n / (3 * p)) (2 * (n / (3 * p)))).filter Nat.Prime) :
    p < q ∧ q.Prime ∧ (n + 2) / 3 ≤ p * q ∧ p * q ≤ 2 * n / 3 := by
  rw [Finset.mem_filter, Finset.mem_Ioc] at hq
  obtain ⟨⟨hq1, hq2⟩, hqp⟩ := hq
  have hp2 := hp.two_le
  have h1 : 3 * p * (n / (3 * p)) ≤ n := Nat.mul_div_le _ _
  have h2 : n < 3 * p * (n / (3 * p) + 1) := Nat.lt_mul_div_succ _ (by omega)
  generalize n / (3 * p) = y at h1 h2 hq1 hq2
  have hpy : p ≤ y := by
    have h4 : 3 * p * p < 3 * p * (y + 1) := lt_of_le_of_lt h3 h2
    have := Nat.lt_of_mul_lt_mul_left h4
    omega
  refine ⟨by omega, hqp, ?_, ?_⟩
  · have h4 : p * (y + 1) ≤ p * q := Nat.mul_le_mul_left p hq1
    have h5 : n < 3 * (p * q) := by nlinarith
    omega
  · have h4 : p * q ≤ p * (2 * y) := Nat.mul_le_mul_left p hq2
    have h5 : 3 * (p * q) ≤ 2 * n := by nlinarith
    omega

theorem refute6808_L3_card_ge (n r : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ r < p ∧ 3 * p * p ≤ n) :
    ∑ p ∈ P, ((Finset.Ioc (n / (3 * p)) (2 * (n / (3 * p)))).filter Nat.Prime).card ≤
    ({u ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) |
        r < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac)} : Finset ℕ).card := by
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun x => x.1 * x.2)
  · intro x hx
    have hx' := Finset.mem_sigma.1 (Finset.mem_coe.1 hx)
    obtain ⟨hpP, hq⟩ := hx'
    obtain ⟨hpp, hrp, h3⟩ := hP _ hpP
    obtain ⟨hlt, hqp, hl, hu⟩ := refute6808_L3_pair n x.1 x.2 hpp h3 hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hl, hu⟩, ?_⟩
    rw [refute6808_L3_minFac hpp hqp hlt, Nat.mul_div_cancel_left _ hpp.pos]
    exact ⟨hrp, hpp, hqp⟩
  · rintro ⟨p, q⟩ hx ⟨p', q'⟩ hx' heq
    have hx1 := Finset.mem_sigma.1 (Finset.mem_coe.1 hx)
    have hx2 := Finset.mem_sigma.1 (Finset.mem_coe.1 hx')
    obtain ⟨hpP, hq⟩ := hx1
    obtain ⟨hpP', hq'⟩ := hx2
    obtain ⟨hpp, hrp, h3⟩ := hP _ hpP
    obtain ⟨hpp', hrp', h3'⟩ := hP _ hpP'
    obtain ⟨hlt, hqp, -, -⟩ := refute6808_L3_pair n p q hpp h3 hq
    obtain ⟨hlt', hqp', -, -⟩ := refute6808_L3_pair n p' q' hpp' h3' hq'
    simp only at heq
    have e1 := refute6808_L3_minFac hpp hqp hlt
    have e2 := refute6808_L3_minFac hpp' hqp' hlt'
    dsimp only at e1 e2
    have hpp2 : p = p' := by
      calc p = (p * q).minFac := e1.symm
        _ = (p' * q').minFac := by rw [heq]
        _ = p' := e2
    subst hpp2
    have : q = q' := Nat.eq_of_mul_eq_mul_left hpp.pos heq
    subst this
    rfl

theorem refute6808_L3_Qbound (c : ℝ) (hc0 : 0 < c) (y0 : ℕ)
    (hc : ∀ y : ℕ, y0 ≤ y → c * (y : ℝ) / Real.log y ≤
      (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ))
    (n p : ℕ) (hp : p.Prime) (hy0 : y0 ≤ p) (h3 : 3 * p * p ≤ n) :
    c * n / (6 * p * Real.log n) ≤
      (((Finset.Ioc (n / (3 * p)) (2 * (n / (3 * p)))).filter Nat.Prime).card : ℝ) := by
  have hp2 := hp.two_le
  have h1 : 3 * p * (n / (3 * p)) ≤ n := Nat.mul_div_le _ _
  have h2 : n < 3 * p * (n / (3 * p) + 1) := Nat.lt_mul_div_succ _ (by omega)
  generalize n / (3 * p) = y at h1 h2 ⊢
  have hpy : p ≤ y := by
    have h4 : 3 * p * p < 3 * p * (y + 1) := lt_of_le_of_lt h3 h2
    have := Nat.lt_of_mul_lt_mul_left h4
    omega
  have hyy0 : y0 ≤ y := le_trans hy0 hpy
  refine le_trans ?_ (hc y hyy0)
  have hy2 : (2:ℝ) ≤ y := by exact_mod_cast le_trans hp2 hpy
  have hyn : y ≤ n := by nlinarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog : Real.log y ≤ Real.log n :=
    Real.log_le_log (by linarith) (by exact_mod_cast hyn)
  have hlogn : 0 < Real.log n := lt_of_lt_of_le hlogy hlog
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hn6 : (n:ℝ) ≤ 6 * p * y := by
    have h' : (n:ℝ) < 3 * p * (y + 1) := by exact_mod_cast h2
    nlinarith [mul_nonneg hpR.le (sub_nonneg.2 (by linarith : (1:ℝ) ≤ y))]
  rw [div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) hpR) hlogn) hlogy]
  have h6 := mul_le_mul hn6 hlog hlogy.le (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h6 hc0.le]

theorem refute6808_L3_pow8 (m : ℕ) : (8:ℕ) ^ (4 * m) = 2 ^ (12 * m) := by
  rw [show (8:ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  ring_nf

theorem refute6808_L3_3pp (m n i p : ℕ) (hn : n = 8 ^ (4 * m)) (hi : i < 5 * m)
    (hp : p ≤ 2 ^ (i + 1)) : 3 * p * p ≤ n := by
  have h1 : p * p ≤ 2 ^ (i + 1) * 2 ^ (i + 1) := Nat.mul_le_mul hp hp
  have h4 : 2 ^ (i + 1) * 2 ^ (i + 1) * 4 = 2 ^ (2 * i + 4) := by ring
  have h5 : 2 ^ (2 * i + 4) ≤ n := by
    rw [hn, refute6808_L3_pow8]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

theorem refute6808_L3_perI (c : ℝ) (hc0 : 0 < c) (y0 : ℕ)
    (hc : ∀ y : ℕ, y0 ≤ y → c * (y : ℝ) / Real.log y ≤
      (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ))
    (m n : ℕ) (hm : 1 ≤ m) (hn : n = 8 ^ (4 * m)) (hy : y0 ≤ 4 * m)
    (i : ℕ) (hi1 : 4 * m ≤ i) (hi2 : i < 5 * m) :
    c ^ 2 * n / (720 * (m:ℝ) ^ 2 * (Real.log 2) ^ 2) ≤
      ∑ p ∈ (Finset.Ioc (2 ^ i) (2 ^ (i + 1))).filter Nat.Prime,
        (((Finset.Ioc (n / (3 * p)) (2 * (n / (3 * p)))).filter Nat.Prime).card : ℝ) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log (n:ℝ) = 12 * m * Real.log 2 := by
    rw [hn]
    push_cast
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, ← pow_mul, Real.log_pow]
    push_cast
    ring
  have h2i : y0 ≤ 2 ^ i := by
    have : i < 2 ^ i := Nat.lt_two_pow_self
    omega
  have hT := hc (2 ^ i) h2i
  have hT' : c * 2 ^ i / (i * Real.log 2) ≤
      (((Finset.Ioc (2 ^ i) (2 ^ (i + 1))).filter Nat.Prime).card : ℝ) := by
    have e : 2 * 2 ^ i = 2 ^ (i + 1) := by ring
    rw [e] at hT
    simpa [Real.log_pow] using hT
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hi0 : (0:ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have him : (i:ℝ) ≤ 5 * m := by exact_mod_cast (by omega : i ≤ 5 * m)
  have hnpos : (0:ℝ) < n := by
    rw [hn]; positivity
  have hB : ∀ p ∈ (Finset.Ioc (2 ^ i) (2 ^ (i + 1))).filter Nat.Prime,
      c * n / (6 * (2 * 2 ^ i) * (12 * m * Real.log 2)) ≤
        (((Finset.Ioc (n / (3 * p)) (2 * (n / (3 * p)))).filter Nat.Prime).card : ℝ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
    have h3 : 3 * p * p ≤ n := refute6808_L3_3pp m n i p hn hi2 hp2
    have hy0 : y0 ≤ p := by omega
    have hQ := refute6808_L3_Qbound c hc0 y0 hc n p hpp hy0 h3
    rw [hlogn] at hQ
    refine le_trans ?_ hQ
    have hpR : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hple : (p:ℝ) ≤ 2 * 2 ^ i := by
      have := (Nat.cast_le (α := ℝ)).2 hp2
      push_cast at this
      rw [pow_succ] at this
      linarith
    apply div_le_div_of_nonneg_left (by positivity)
    · exact mul_pos (mul_pos (by norm_num) hpR) (by positivity)
    · have : 0 < 12 * (m:ℝ) * Real.log 2 := by positivity
      nlinarith
  have hs := Finset.card_nsmul_le_sum _ _ _ hB
  rw [nsmul_eq_mul] at hs
  refine le_trans ?_ hs
  have hBnn : 0 ≤ c * n / (6 * (2 * 2 ^ i) * (12 * m * Real.log 2)) := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hT' hBnn)
  have eq : c * 2 ^ i / (i * Real.log 2) *
      (c * n / (6 * (2 * 2 ^ i) * (12 * m * Real.log 2))) =
      c ^ 2 * n / (144 * i * m * Real.log 2 ^ 2) := by
    field_simp
    ring
  rw [eq]
  apply div_le_div_of_nonneg_left (by positivity)
  · have : 0 < (144:ℝ) * i * m := by positivity
    exact mul_pos this (by positivity)
  · have h := mul_le_mul_of_nonneg_right him hm0.le
    have h' := mul_le_mul_of_nonneg_right h (sq_nonneg (Real.log 2))
    nlinarith

theorem refute6808_L3_x3_lower (c : ℝ) (hc0 : 0 < c) (y0 : ℕ)
    (hc : ∀ y : ℕ, y0 ≤ y → c * (y : ℝ) / Real.log y ≤
      (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ))
    (m n : ℕ) (hm : 1 ≤ m) (hn : n = 8 ^ (4 * m)) (hy : y0 ≤ 4 * m) :
    c ^ 2 * n / (720 * (m:ℝ) * (Real.log 2) ^ 2) ≤
      (({u ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) |
        2 ^ (4 * m) < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac)} :
        Finset ℕ).card : ℝ) := by
  have hdisj : ((Finset.range m : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.Ioc (2 ^ (4 * m + j)) (2 ^ (4 * m + j + 1))).filter Nat.Prime) := by
    intro j _ j' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp hp'
    rcases lt_or_gt_of_ne hne with h | h
    · have : 2 ^ (4 * m + j + 1) ≤ 2 ^ (4 * m + j') :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : 2 ^ (4 * m + j' + 1) ≤ 2 ^ (4 * m + j) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hsum := Finset.sum_biUnion (f := fun p : ℕ =>
      (((Finset.Ioc (n / (3 * p)) (2 * (n / (3 * p)))).filter Nat.Prime).card : ℝ)) hdisj
  have hP : ∀ p ∈ (Finset.range m).biUnion
      (fun j => (Finset.Ioc (2 ^ (4 * m + j)) (2 ^ (4 * m + j + 1))).filter Nat.Prime),
      p.Prime ∧ 2 ^ (4 * m) < p ∧ 3 * p * p ≤ n := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨j, hj, hpj⟩ := hp
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_Ioc] at hpj
    obtain ⟨⟨h1, h2⟩, h3⟩ := hpj
    have : 2 ^ (4 * m) ≤ 2 ^ (4 * m + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨h3, by omega, refute6808_L3_3pp m n (4 * m + j) p hn (by omega) h2⟩
  have hge := refute6808_L3_card_ge n (2 ^ (4 * m)) _ hP
  have hge' : (∑ p ∈ (Finset.range m).biUnion
      (fun j => (Finset.Ioc (2 ^ (4 * m + j)) (2 ^ (4 * m + j + 1))).filter Nat.Prime),
      (((Finset.Ioc (n / (3 * p)) (2 * (n / (3 * p)))).filter Nat.Prime).card : ℝ)) ≤
      (({u ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) |
        2 ^ (4 * m) < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac)} :
        Finset ℕ).card : ℝ) := by
    exact_mod_cast hge
  rw [hsum] at hge'
  refine le_trans ?_ hge'
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hsl := Finset.sum_le_sum (s := Finset.range m)
    (f := fun _ => c ^ 2 * (n:ℝ) / (720 * (m:ℝ) ^ 2 * (Real.log 2) ^ 2))
    (g := fun j => ∑ p ∈ (Finset.Ioc (2 ^ (4 * m + j)) (2 ^ (4 * m + j + 1))).filter Nat.Prime,
      (((Finset.Ioc (n / (3 * p)) (2 * (n / (3 * p)))).filter Nat.Prime).card : ℝ))
    (fun j hj => refute6808_L3_perI c hc0 y0 hc m n hm hn hy (4 * m + j) (by omega)
      (by rw [Finset.mem_range] at hj; omega))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsl
  refine le_trans (le_of_eq ?_) hsl
  field_simp

theorem refute6808_L3_floor (k : ℕ) : ⌊((8 ^ k : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊ = 2 ^ k := by
  have h : ((8 ^ k : ℕ) : ℝ) = ((2:ℝ) ^ k) ^ 3 := by
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h, show (1 / 3 : ℝ) = ((3:ℕ):ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  exact_mod_cast Nat.floor_natCast (2 ^ k)

theorem refute6808_L3_x4_upper (C : ℝ) (hC : 0 < C)
    (hL1 : ∀ y : ℕ, 2 ≤ y →
      ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 3 y), (1 - 2 / (p : ℝ)) ≤ C / (Real.log y) ^ 2)
    (m n : ℕ) (hm : 1 ≤ m) (hn : n = 8 ^ (4 * m)) :
    (↑(Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) * (↑n.totient : ℝ) / (↑n : ℝ) *
      ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬x5 ∣ n,
        ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)) ≤
    (n:ℝ) * (1 / 2) * (C / (6 * m * Real.log 2) ^ 2) := by
  have h12 := refute6808_L3_pow8 m
  have hsq : n.sqrt = 2 ^ (6 * m) := by
    have : n = 2 ^ (6 * m) * 2 ^ (6 * m) := by
      rw [hn, h12, ← pow_add]; ring_nf
    rw [this]
    exact Nat.sqrt_eq _
  have hsq2 : 2 ≤ n.sqrt := by
    rw [hsq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (6 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hS : Finset.filter (fun x5 => ¬x5 ∣ n) (Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt)) =
      Finset.filter Nat.Prime (Finset.Icc 3 n.sqrt) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h2, hs⟩, hp⟩, hnd⟩
      refine ⟨⟨?_, hs⟩, hp⟩
      by_contra hlt
      have : x = 2 := by omega
      apply hnd
      rw [this, hn]
      exact dvd_pow (by norm_num) (by omega)
    · rintro ⟨⟨h3, hs⟩, hp⟩
      refine ⟨⟨⟨by omega, hs⟩, hp⟩, ?_⟩
      intro hd
      rw [hn, h12] at hd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
      omega
  rw [hS]
  have hprod := hL1 n.sqrt hsq2
  have hlog : Real.log (n.sqrt : ℝ) = 6 * m * Real.log 2 := by
    rw [hsq]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog] at hprod
  have hnn : 0 ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 3 n.sqrt), (1 - 2 / (p : ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have : (3:ℝ) ≤ p := by exact_mod_cast hp.1.1
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hphi : (n.totient : ℝ) * 2 = n := by
    have h1 : n = 2 ^ (12 * m) := by rw [hn, h12]
    have h2 := Nat.totient_prime_pow Nat.prime_two (show 0 < 12 * m by omega)
    rw [h1, h2]
    have : 2 ^ (12 * m) = 2 * 2 ^ (12 * m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have thisR : (2:ℝ) ^ (12 * m) = 2 * 2 ^ (12 * m - 1) := by exact_mod_cast this
    push_cast
    rw [thisR]
    ring
  have hnpos : (0:ℝ) < n := by
    rw [hn]; positivity
  have hcard : ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) ≤ n := by
    rw [Nat.card_Icc]
    have hn1 : 1 ≤ n := by
      rw [hn]
      exact Nat.one_le_pow _ _ (by norm_num)
    have : 2 * n / 3 + 1 - (n + 2) / 3 ≤ n := by omega
    exact_mod_cast this
  have hq : ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) * (n.totient : ℝ) / (n : ℝ) ≤
      (n:ℝ) * (1 / 2) := by
    have : (n.totient : ℝ) = n / 2 := by linarith
    rw [this]
    field_simp
    nlinarith [hcard]
  have hlogpos : 0 < 6 * (m:ℝ) * Real.log 2 := by
    have : (0:ℝ) < m := by exact_mod_cast hm
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hdnn : 0 ≤ C / (6 * (m:ℝ) * Real.log 2) ^ 2 := by positivity
  exact mul_le_mul hq hprod hnn (by positivity)

theorem refute6808_L3_main (C c : ℝ) (hC : 0 < C) (hc0 : 0 < c) (y0 : ℕ)
    (hL1 : ∀ y : ℕ, 2 ≤ y →
      ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 3 y), (1 - 2 / (p : ℝ)) ≤ C / (Real.log y) ^ 2)
    (hc : ∀ y : ℕ, y0 ≤ y → c * (y : ℝ) / Real.log y ≤
      (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ))
    (m n : ℕ) (hm : 1 ≤ m) (hn : n = 8 ^ (4 * m)) (hy : y0 ≤ 4 * m)
    (hbig : 23 * C / (5 * c ^ 2) < m) :
    (23 / 50 : ℝ) * ((↑(Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) *
      (↑n.totient : ℝ) / (↑n : ℝ) *
      ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt)
        with ¬x5 ∣ n, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ))) <
    (({u ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) |
        ⌊(↑n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧
          Nat.Prime (u / u.minFac)} : Finset ℕ).card : ℝ) := by
  have hf : ⌊(↑n : ℝ) ^ (1 / 3 : ℝ)⌋₊ = 2 ^ (4 * m) := by
    rw [hn]
    exact refute6808_L3_floor _
  rw [hf]
  have h3 := refute6808_L3_x3_lower c hc0 y0 hc m n hm hn hy
  have h4 := refute6808_L3_x4_upper C hC hL1 m n hm hn
  refine lt_of_lt_of_le ?_ h3
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left h4 (by norm_num)) ?_
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hnpos : (0:ℝ) < (n : ℝ) := by
    rw [hn]; positivity
  generalize (n : ℝ) = N at hnpos ⊢
  have hc2 : 0 < c ^ 2 := by positivity
  have hbig' : 23 * C < 5 * c ^ 2 * m := by
    rw [div_lt_iff₀ (by positivity)] at hbig
    linarith
  have e1 : (23 / 50 : ℝ) * (N * (1 / 2) * (C / (6 * m * Real.log 2) ^ 2)) =
      23 * C * N / (3600 * m ^ 2 * Real.log 2 ^ 2) := by
    field_simp
    ring
  have e2 : c ^ 2 * N / (720 * (m:ℝ) * Real.log 2 ^ 2) =
      5 * c ^ 2 * m * N / (3600 * m ^ 2 * Real.log 2 ^ 2) := by
    field_simp
    ring
  rw [e1, e2]
  apply div_lt_div_of_pos_right _ (by positivity)
  nlinarith

theorem Conjectures.Cuts.Refute25dd470ddb6f861c24eaee19 : ¬ (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → Even x6 → (↑(x3 x6).card : ℝ) ≤ (23 / 50 : ℝ) * x4 x6) := by
  rintro ⟨N0, hN0⟩
  obtain ⟨C, hC, hL1⟩ := refute6808_L1
  obtain ⟨c, hc0, y0, hc⟩ := refute6808_L2
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ : ∃ m : ℕ, 1 ≤ m ∧ N0 ≤ m ∧ y0 ≤ 4 * m ∧
      23 * C / (5 * c ^ 2) < m := by
    refine ⟨⌈23 * C / (5 * c ^ 2)⌉₊ + N0 + y0 + 1, by omega, by omega, by omega, ?_⟩
    have := Nat.le_ceil (23 * C / (5 * c ^ 2))
    push_cast
    have h0 : (0:ℝ) ≤ N0 := Nat.cast_nonneg _
    have h1 : (0:ℝ) ≤ y0 := Nat.cast_nonneg _
    linarith
  have hge : N0 ≤ 8 ^ (4 * m) := by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ m ≤ 8 ^ (4 * m) := by
      calc 2 ^ m ≤ 8 ^ m := Nat.pow_le_pow_left (by norm_num) m
        _ ≤ 8 ^ (4 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hev : Even (8 ^ (4 * m)) := Nat.even_pow.2 ⟨⟨4, by norm_num⟩, by omega⟩
  exact absurd (hN0 (8 ^ (4 * m)) hge hev)
    (not_le.2 (refute6808_L3_main C c hC hc0 y0 hL1 hc m (8 ^ (4 * m)) hm1 rfl hm3 hm4))
