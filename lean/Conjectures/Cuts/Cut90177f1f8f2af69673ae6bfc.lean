import Mathlib

/-! ## A fixed-scale fourth-moment route to the four-sevenths exceptional-set bound

The two inputs are the positive major-arc coefficient of Li–Liu (arXiv:2610.26756,
Proposition 4.1) and their minor-arc fourth moment (Theorem 1). They concern the
same smoothed sum on a fixed scale, with one choice of denominator exponent from
(4/9, 9/20). The explicit smooth weight is supported in [1/16,15/16] and
equals 1 on [1/8,7/8]. Integer translates of the rational centers make the arcs
periodic. These paper estimates are inputs, not theorems established by this file.

This route differs from #4200 and #4519: it keeps the Fourier polynomial and arcs
fixed as n varies. The Parseval step follows the community's FrozenMinorBessel
and AlmostAllExceptionDensity files. We identify exceptional coefficients by
finite additive orthogonality, use the fixed major-arc floor, and sum the dyadic
estimates to obtain the frozen bound.
-/
open MeasureTheory Filter
open scoped BigOperators
open scoped Topology

-- child 1 zh: 在指定平滑素数和的固定主弧上，每个充分大二进区间内的偶数目标均有正线性下界。
-- child 1 en: Positive linear major-arc coefficients on the same scale for all even targets in each upper dyadic block.
-- child 2 zh: 存在一个允许的分母指数，使该平滑素数和在同一尺度的次弧四阶矩满足平方根级例外集所需的估计。
-- child 2 en: For some admissible denominator exponent, the complementary fourth moment is bounded by a constant times X^(5/2) log(X)^100.

set_option maxHeartbeats 1200000 in
theorem Conjectures.Cuts.Cut90177f1f8f2af69673ae6bfc
    (h₁ : let S := fun (X : ℕ) (t : ℝ) =>
      ∑ p ∈ (Finset.range (X+1)).filter Nat.Prime,
        ((Real.log (p : ℝ) * (Real.smoothTransition (16*((p : ℝ)/X)-1) *
          Real.smoothTransition (15-16*((p : ℝ)/X))) : ℝ) : ℂ) *
          fourier (p : ℤ) (t : AddCircle (1 : ℝ))
    let A := fun (k : ℝ) (X : ℕ) =>
      ⋃ (q : ℕ) (a : ℤ), if 1 ≤ q ∧ (q : ℝ) ≤ (X : ℝ)^k ∧ Nat.Coprime a.natAbs q then
        Set.Icc ((a : ℝ)/q-(X : ℝ)^k/(q*X)) ((a : ℝ)/q+(X : ℝ)^k/(q*X)) else ∅
    ∀ k : ℝ, (4:ℝ)/9 < k → k < (9:ℝ)/20 → ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ,
      ∀ X ≥ X₀, ∀ n ∈ Finset.Ioc (X/2) X, Even n →
        c*X ≤ (fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1)
          ((A k X).indicator (fun t => (S X t)^2)) (n : ℤ)).re)
    (h₂ : let S := fun (X : ℕ) (t : ℝ) =>
      ∑ p ∈ (Finset.range (X+1)).filter Nat.Prime,
        ((Real.log (p : ℝ) * (Real.smoothTransition (16*((p : ℝ)/X)-1) *
          Real.smoothTransition (15-16*((p : ℝ)/X))) : ℝ) : ℂ) *
          fourier (p : ℤ) (t : AddCircle (1 : ℝ))
    let A := fun (k : ℝ) (X : ℕ) =>
      ⋃ (q : ℕ) (a : ℤ), if 1 ≤ q ∧ (q : ℝ) ≤ (X : ℝ)^k ∧ Nat.Coprime a.natAbs q then
        Set.Icc ((a : ℝ)/q-(X : ℝ)^k/(q*X)) ((a : ℝ)/q+(X : ℝ)^k/(q*X)) else ∅
    ∃ k : ℝ, (4:ℝ)/9 < k ∧ k < (9:ℝ)/20 ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ,
      ∀ X ≥ X₀, intervalIntegral ((A k X)ᶜ.indicator (fun t => ‖S X t‖^4))
        0 1 MeasureTheory.volume ≤ C*(X : ℝ)^((5 : ℝ)/2)*(Real.log (X : ℝ))^100) :
    let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ) ≤ C * (X:ℝ) ^ (4/7 + e) := by
  classical
  let S := fun (X : ℕ) (t : ℝ) =>
        ∑ p ∈ (Finset.range (X+1)).filter Nat.Prime,
          ((Real.log (p : ℝ) * (Real.smoothTransition (16*((p : ℝ)/X)-1) *
            Real.smoothTransition (15-16*((p : ℝ)/X))) : ℝ) : ℂ) *
            fourier (p : ℤ) (t : AddCircle (1 : ℝ))
  let A := fun (k : ℝ) (X : ℕ) =>
        ⋃ (q : ℕ) (a : ℤ), if 1 ≤ q ∧ (q : ℝ) ≤ (X : ℝ)^k ∧ Nat.Coprime a.natAbs q then
          Set.Icc ((a : ℝ)/q-(X : ℝ)^k/(q*X)) ((a : ℝ)/q+(X : ℝ)^k/(q*X)) else ∅
  intro bad
  let _ : DecidablePred bad := Classical.decPred bad
  have splitCoefficient (H : ℝ → ℂ) (hH : Continuous H)
      (A : Set ℝ) (hA : MeasurableSet A) (n : ℤ) :
      fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (A.indicator H) n +
        fourierCoeffOn zero_lt_one (Aᶜ.indicator H) n =
        fourierCoeffOn zero_lt_one H n := by
    classical
    rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
      ← smul_add]
    congr 1
    let g (t : ℝ) := fourier (-n) (t : AddCircle ((1 : ℝ)-0)) • H t
    have hg : Continuous g :=
      ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).smul hH
    have move (s : Set ℝ) : (fun t : ℝ =>
        fourier (-n) (t : AddCircle ((1 : ℝ)-0)) • s.indicator H t) = s.indicator g := by
      funext t
      by_cases ht : t ∈ s <;> simp [g, ht]
    rw [move A, move Aᶜ]
    have hi (s : Set ℝ) (hs : MeasurableSet s) :
        IntervalIntegrable (s.indicator g) volume 0 1 :=
      ⟨(hg.intervalIntegrable 0 1).1.indicator hs, (hg.intervalIntegrable 0 1).2.indicator hs⟩
    rw [← intervalIntegral.integral_add (hi A hA) (hi Aᶜ hA.compl)]
    apply intervalIntegral.integral_congr
    intro t _
    by_cases ht : t ∈ A <;> simp [ht, g]
  have count_mul_floor_sq_le_fourth (H : ℝ → ℂ) (hH : Continuous H)
      (A : Set ℝ) (hA : MeasurableSet A) (F : Finset ℕ) (T : ℝ) (hT : 0 ≤ T)
      (hzero : ∀ n ∈ F, fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1)
        (fun t => (H t)^2) (n : ℤ) = 0)
      (hmajor : ∀ n ∈ F, T ≤ (fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1)
        (A.indicator (fun t => (H t)^2)) (n : ℤ)).re) :
      (F.card : ℝ) * T^2 ≤ ∫ t in (0 : ℝ)..1, Aᶜ.indicator (fun x => ‖H x‖^4) t := by
    classical
    let f := Aᶜ.indicator (fun t => (H t)^2)
    have mem : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      apply MemLp.indicator hA.compl.nullMeasurableSet
      apply (memLp_two_iff_integrable_sq_norm (hH.pow 2).aestronglyMeasurable).2
      exact ((((hH.pow 2).norm.pow 2).intervalIntegrable (μ := volume) 0 1)).1
    let coeff (n : ℤ) := fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) f n
    have floorSq (n : ℕ) (hn : n ∈ F) : T^2 ≤ ‖coeff n‖^2 := by
      have hs := splitCoefficient (fun t => (H t)^2) (hH.pow 2) A hA n
      rw [hzero n hn] at hs
      have hneg := congrArg Complex.re hs
      rw [Complex.add_re, Complex.zero_re] at hneg
      have hm := hmajor n hn
      change _ + (coeff n).re = 0 at hneg
      apply pow_le_pow_left₀ hT
      have : T ≤ -(coeff n).re := by linarith
      exact this.trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
    let embed : ℕ ↪ ℤ := ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
    have bound := sum_le_hasSum (F.map embed)
      (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one f i‖)
      (hasSum_sq_fourierCoeffOn zero_lt_one mem)
    have mask (t : ℝ) : ‖f t‖^2 = Aᶜ.indicator (fun x => ‖H x‖^4) t := by
      by_cases ht : t ∈ Aᶜ
      · simp only [f, Set.indicator_of_mem ht, norm_pow]; ring
      · simp [f, ht]
    simp only [Finset.sum_map, sub_zero, inv_one, one_smul, mask] at bound
    calc
      (F.card : ℝ) * T^2 = ∑ _n ∈ F, T^2 := by simp [nsmul_eq_mul]
      _ ≤ ∑ n ∈ F, ‖coeff n‖^2 := Finset.sum_le_sum floorSq
      _ ≤ _ := bound
  have arcsMeasurable (k : ℝ) (X : ℕ) : MeasurableSet (A k X) := by
    classical
    apply MeasurableSet.iUnion; intro q
    apply MeasurableSet.iUnion; intro a
    split <;> simp [measurableSet_Icc]
  have sumContinuous (X : ℕ) : Continuous (S X) := by
    apply continuous_finsetSum
    intro p _
    exact continuous_const.mul ((fourier (p : ℤ)).continuous.comp (AddCircle.continuous_mk' 1))
  have cancelScale {m X : ℕ} {c C : ℝ} (hc : 0 < c) (hX : 0 < X)
      (h : (m : ℝ) * (c * X)^2 ≤ C * (X : ℝ)^((5 : ℝ)/2) * (Real.log (X : ℝ))^100) :
      (m : ℝ) ≤ C / c^2 * Real.sqrt X * (Real.log (X : ℝ))^100 := by
    have hx : 0 < (X : ℝ) := by exact_mod_cast hX
    have power : (X : ℝ)^((5 : ℝ)/2) = (X : ℝ)^2 * Real.sqrt X := by
      rw [show (5 : ℝ)/2 = (2 : ℕ) + (1 : ℝ)/2 by norm_num, Real.rpow_add hx,
        Real.rpow_natCast, Real.sqrt_eq_rpow]
    calc
      (m : ℝ) ≤ (C * (X : ℝ)^((5 : ℝ)/2) * (Real.log (X : ℝ))^100) / (c*X)^2 :=
        (le_div_iff₀ (by positivity)).2 h
      _ = _ := by rw [power]; field_simp
  let primeSum (P : Finset ℕ) (w : ℕ → ℂ) (x : AddCircle (1 : ℝ)) : ℂ :=
    ∑ p ∈ P, w p * fourier (p : ℤ) x
  have coeff_sq_eq_zero (P : Finset ℕ) (w : ℕ → ℂ) (n : ℕ)
      (h : ∀ p ∈ P, ∀ q ∈ P, p + q ≠ n) :
      fourierCoeff (fun x => (primeSum P w x)^2) (n : ℤ) = 0 := by
    classical
    let F (y : ℕ × ℕ) (x : AddCircle (1 : ℝ)) : ℂ :=
      (w y.1 * w y.2) * fourier ((y.1 : ℤ) + (y.2 : ℤ)) x
    have expand : (fun x => (primeSum P w x)^2) = ∑ y ∈ P ×ˢ P, F y := by
      funext x
      dsimp only [primeSum]
      rw [sq, Finset.sum_mul_sum, Finset.sum_apply, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      simp only [F, fourier_add]
      ring
    have integrableF (y : ℕ × ℕ) : Integrable (F y) AddCircle.haarAddCircle :=
      (continuous_const.mul (fourier ((y.1 : ℤ) + (y.2 : ℤ))).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [expand, fourierCoeff.sum _ _ (fun y _ => integrableF y), Finset.sum_apply]
    apply Finset.sum_eq_zero
    rintro ⟨p, q⟩ hpq
    have hpn := h p (Finset.mem_product.mp hpq).1 q (Finset.mem_product.mp hpq).2
    have hneq : (n : ℤ) ≠ (p : ℤ) + q := by omega
    simp only [F, fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_eq_of_ne hneq, mul_zero]
  have interval_coeff_sq_eq_zero (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
      (w : ℕ → ℂ) (n : ℕ) (hex : ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) :
      fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1)
        (fun t : ℝ => (primeSum P w (t : AddCircle (1 : ℝ)))^2) (n : ℤ) = 0 := by
    have hz := coeff_sq_eq_zero P w n (fun p hp q hq h => hex ⟨p, q, hP p hp, hP q hq, h⟩)
    rw [fourierCoeff_eq_intervalIntegral _ _ (0 : ℝ)] at hz
    rw [fourierCoeffOn_eq_integral]
    simp only [fourier_coe_apply, sub_zero, zero_add, Complex.ofReal_one, div_one] at hz ⊢
    exact hz
  have initial_bound_of_window (P : ℕ → Prop) [DecidablePred P]
      {s A : ℝ} {K : ℕ} (hs : 0 < s)
      (h : ∀ X : ℕ, K ≤ X →
        ((((Finset.Ioc (X / 2) X).filter P).card : ℝ)) ≤ A * (X : ℝ) ^ s) :
      ∃ D : ℝ, 0 < D ∧ ∀ X : ℕ,
        ((((Finset.Icc 4 X).filter P).card : ℝ)) ≤ D * (X : ℝ) ^ s := by
    let r : ℝ := (1 / 2 : ℝ) ^ s
    have hr : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs
    let D := max ((K : ℝ) + 1) (A / (1 - r))
    have hK : (K : ℝ) + 1 ≤ D := le_max_left _ _
    have hD : 0 < D := lt_of_lt_of_le (by positivity) hK
    have hA : A ≤ D * (1 - r) := (div_le_iff₀ (sub_pos.mpr hr)).mp (le_max_right _ _)
    refine ⟨D, hD, ?_⟩
    intro X
    induction X using Nat.strong_induction_on with
    | ind X ih =>
      by_cases hX : X = 0
      · simp [hX, Real.zero_rpow hs.ne']
      have hone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
      by_cases hlarge : K ≤ X
      · have hprev := ih (X / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hX) (by decide : 1 < 2))
        have hsub : (Finset.Icc 4 X).filter P ⊆
            (Finset.Icc 4 (X / 2)).filter P ∪ (Finset.Ioc (X / 2) X).filter P := by
          intro n hn
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc] at *
          by_cases hhalf : n ≤ X / 2
          · exact Or.inl ⟨⟨hn.1.1,hhalf⟩, hn.2⟩
          · exact Or.inr ⟨⟨lt_of_not_ge hhalf,hn.1.2⟩,hn.2⟩
        have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hcast : ((X / 2 : ℕ) : ℝ) * 2 ≤ (X : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self X 2
        have hpow : ((X / 2 : ℕ) : ℝ) ^ s ≤ (X : ℝ) ^ s * r := by
          dsimp [r]
          rw [← Real.mul_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 1 / 2)]
          exact Real.rpow_le_rpow (by positivity) (by linarith) hs.le
        calc
          ((((Finset.Icc 4 X).filter P).card : ℝ)) ≤
              ((((Finset.Icc 4 (X / 2)).filter P).card : ℝ)) +
              ((((Finset.Ioc (X / 2) X).filter P).card : ℝ)) := by exact_mod_cast hcard
          _ ≤ D * ((X / 2 : ℕ) : ℝ) ^ s + A * (X : ℝ) ^ s := add_le_add hprev (h X hlarge)
          _ ≤ D * ((X : ℝ) ^ s * r) + A * (X : ℝ) ^ s := by gcongr
          _ = (D*r + A) * (X : ℝ)^s := by ring
          _ ≤ D * (X : ℝ)^s := mul_le_mul_of_nonneg_right (by linarith [hA]) (by positivity)
      · have hcount : ((Finset.Icc 4 X).filter P).card ≤ X := by
          refine (Finset.card_filter_le _ _).trans ?_
          rw [Nat.card_Icc]
          omega
        calc
          ((((Finset.Icc 4 X).filter P).card : ℝ)) ≤ (X : ℝ) := by exact_mod_cast hcount
          _ ≤ D := by have hxk : (X : ℝ) ≤ K := by exact_mod_cast (show X ≤ K by omega)
                      linarith
          _ ≤ D * (X : ℝ)^s := by
            simpa using mul_le_mul_of_nonneg_left (Real.one_le_rpow hone hs.le) hD.le
  have eventual_sqrt_log_le_four_sevenths :
      ∀ᶠ X : ℕ in atTop, Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ (100 : ℕ) ≤
        (X : ℝ)^((4 : ℝ)/7) := by
    have hlog := (isLittleO_log_rpow_rpow_atTop (s := (1:ℝ)/14) 100 (by norm_num)).bound
      (by norm_num : (0:ℝ) < 1)
    have hnat := tendsto_natCast_atTop_atTop.eventually hlog
    filter_upwards [hnat, eventually_ge_atTop (1:ℕ)] with n hb hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    change ‖Real.log (n : ℝ) ^ (100 : ℝ)‖ ≤ 1 * ‖(n : ℝ) ^ ((1 : ℝ) / 14)‖ at hb
    rw [show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg hn'.le _)] at hb
    have hin : (Real.log (n : ℝ)) ^ (100:ℕ) ≤ (n:ℝ)^((1:ℝ)/14) := by
      exact
        (le_abs_self ((Real.log (n : ℝ)) ^ (100:ℕ))).trans hb
    calc
      Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (100 : ℕ) ≤
          (n : ℝ)^((1:ℝ)/2) * (n : ℝ)^((1:ℝ)/14) := by
            rw [← Real.sqrt_eq_rpow]
            gcongr
      _ = _ := by rw [← Real.rpow_add hn']; norm_num
  have four_sevenths_of_sqrt_log_windows (P : ℕ → Prop) [DecidablePred P]
      {A : ℝ} (hA : 0 ≤ A)
      (h : ∀ᶠ X : ℕ in atTop, (((Finset.Ioc (X / 2) X).filter P).card : ℝ) ≤
        A * (Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ (100 : ℕ))) :
      ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X →
        (((Finset.Icc 4 X).filter P).card : ℝ) ≤ C * (X : ℝ)^((4 : ℝ)/7 + e) := by
    have hw : ∀ᶠ X : ℕ in atTop, (((Finset.Ioc (X / 2) X).filter P).card : ℝ) ≤
        A * (X : ℝ)^((4 : ℝ)/7) := by
      filter_upwards [h, eventual_sqrt_log_le_four_sevenths] with X hX hlog
      exact hX.trans (mul_le_mul_of_nonneg_left hlog hA)
    obtain ⟨K, hK⟩ := eventually_atTop.1 hw
    obtain ⟨C,hC,hbound⟩ := initial_bound_of_window P (by norm_num : (0:ℝ) < 4/7) hK
    intro e he
    refine ⟨C, 1, hC, ?_⟩
    intro X hX
    refine (hbound X).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) (by linarith)
  obtain ⟨k, hk₁, hk₂, C, hC, Xm, hminor⟩ := h₂
  obtain ⟨c, hc, XM, hmajor⟩ := h₁ k hk₁ hk₂
  apply four_sevenths_of_sqrt_log_windows bad (A := C / c^2) (by positivity)
  filter_upwards [eventually_ge_atTop XM, eventually_ge_atTop Xm,
    eventually_ge_atTop (1 : ℕ)] with X hXM hXm hX
  let F := (Finset.Ioc (X/2) X).filter bad
  have hz (n : ℕ) (hn : n ∈ F) :
      fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (fun t => (S X t)^2) (n : ℤ) = 0 := by
    have he : bad n := (Finset.mem_filter.mp hn).2
    exact interval_coeff_sq_eq_zero ((Finset.range (X+1)).filter Nat.Prime)
      (fun _ hp => (Finset.mem_filter.mp hp).2)
      (fun p => ((Real.log (p : ℝ) * (Real.smoothTransition (16*((p : ℝ)/X)-1) *
        Real.smoothTransition (15-16*((p : ℝ)/X))) : ℝ) : ℂ)) n he.2.2
  have hf (n : ℕ) (hn : n ∈ F) :
      c*X ≤ (fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1)
        ((A k X).indicator (fun t => (S X t)^2)) (n : ℤ)).re :=
    hmajor X hXM n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2.2.1
  have estimate := count_mul_floor_sq_le_fourth (S X) (sumContinuous X) (A k X)
    (arcsMeasurable k X) F (c*X) (by positivity) hz hf
  simpa only [mul_assoc] using cancelScale hc hX (estimate.trans (hminor X hXm))
