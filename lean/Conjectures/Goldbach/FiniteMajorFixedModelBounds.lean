import Mathlib

noncomputable section

namespace FixedModelBoundsBlueprint

set_option maxRecDepth 100000 in
def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

set_option maxRecDepth 100000 in
def J (h : ℝ) (f : ℝ → ℂ) : ℂ :=
  intervalIntegral f (-h) h MeasureTheory.volume

set_option maxRecDepth 100000 in
def Jr (h : ℝ) (f : ℝ → ℝ) : ℝ :=
  intervalIntegral f (-h) h MeasureTheory.volume

set_option maxRecDepth 100000 in
def V (n : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, E ((k : ℝ) * β)

set_option maxRecDepth 100000 in
def M (n q : ℕ) (β : ℝ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * V n β

set_option maxRecDepth 100000 in
def H (n q : ℕ) : ℝ :=
  (105 : ℝ) / ((q : ℝ) * (n : ℝ))

set_option maxRecDepth 100000 in
def Q : Finset ℕ := Finset.Icc (1 : ℕ) 105

set_option maxRecDepth 100000 in
def A (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun a => Nat.Coprime a q)

set_option maxRecDepth 100000 in
def B (n : ℕ) : ℝ :=
  ∑ q ∈ Q, ((A q).card : ℝ) * Jr (H n q) (fun β => ‖M n q β‖ ^ 2)

set_option maxRecDepth 100000 in
def C (n : ℕ) : ℝ :=
  ∑ q ∈ Q, ∑ a ∈ A q,
    (J (H n q) (fun β =>
      (M n q β) ^ 2 * E (-(n : ℝ) * ((a : ℝ) / q + β)))).re

set_option maxRecDepth 100000 in
def R (q n : ℕ) : ℝ :=
  ∑ d ∈ q.divisors.filter (fun d => d ∣ n),
    (d : ℝ) * (ArithmeticFunction.moebius (q / d) : ℝ)

set_option maxRecDepth 100000 in
def K (h : ℝ) : ℝ :=
  Jr h (fun t => Real.sinc (Real.pi * t) ^ 2)

set_option maxRecDepth 100000 in
def S (n q : ℕ) : ℝ :=
  (J (H n q) (fun β => (V n β) ^ 2 * E (-(n : ℝ) * β))).re / (n : ℝ)

set_option maxRecDepth 100000 in
def T (n q : ℕ) : ℝ :=
  Jr (H n q) (fun β => ‖V n β‖ ^ 2) / (n : ℝ)

set_option maxRecDepth 100000 in
def signedCoeff (q n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 * R q n

set_option maxRecDepth 100000 in
def energyCoeff (q : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ)

end FixedModelBoundsBlueprint

set_option maxRecDepth 100000 in
theorem reduced_numerator_phase_sum_aux_complete (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ Finset.range m, FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) : FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold FixedModelBoundsBlueprint.E
    push_cast
    congr 1
    field_simp
  simp_rw [hpow]
  by_cases h : m ∣ a
  · simp [h, hz.mpr h]
  · simp only [h, ite_false]
    have hzm : z ^ m = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (m : ℂ) * (2 * Real.pi * Complex.I * a / m) =
          a * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [harg]
      exact Complex.exp_nat_mul_two_pi_mul_I a
    have hsum := geom_sum_mul z m
    rw [hzm, sub_self] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right
      (sub_ne_zero.mpr (fun hz1 => h (hz.mp hz1)))

set_option maxRecDepth 100000 in
theorem reduced_numerator_phase_sum_aux_coprime_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime b q then 1 else 0 := by
  have hg : Nat.gcd b q ≠ 0 := (Nat.gcd_pos_of_pos_right b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (Nat.gcd b q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff, and_comm]
  rw [← Finset.sum_filter, hs]
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (Nat.gcd b q)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

set_option maxRecDepth 100000 in
theorem reduced_numerator_phase_sum_aux_multiples (q a d : ℕ) (hq : 0 < q)
    (hd : d ∣ q) :
    ∑ b ∈ (Finset.range q).filter (fun b => d ∣ b),
        FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← reduced_numerator_phase_sum_aux_complete m a hm]
  symm
  apply Finset.sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hj) hd),
        dvd_mul_right d j⟩
  · intro k hk
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr
      (by simpa [Nat.mul_comm] using Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hk).2
  · intro j _
    unfold FixedModelBoundsBlueprint.E
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

set_option maxRecDepth 100000 in
theorem reduced_numerator_phase_sum_aux_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ FixedModelBoundsBlueprint.A q,
        FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ Finset.range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) := by
      simp only [reduced_numerator_phase_sum_aux_coprime_indicator q _ hq,
        FixedModelBoundsBlueprint.A, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ Finset.range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← reduced_numerator_phase_sum_aux_multiples q a d hq
        (Nat.dvd_of_mem_divisors hd), Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]

set_option maxRecDepth 100000 in
theorem reduced_numerator_phase_sum_aux_divisor (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ FixedModelBoundsBlueprint.A q,
        FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := by
  rw [reduced_numerator_phase_sum_aux_sum q a hq]
  let f : ℕ → ℂ := fun d =>
    if d ∣ a then (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0
  calc
    (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0)) =
        ∑ d ∈ q.divisors, f (q / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hcomp : q / (q / d) = d :=
        Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq.ne'
      unfold f
      rw [hcomp]
      by_cases ha : q / d ∣ a <;> simp [ha]
      ring
    _ = ∑ d ∈ q.divisors, f d := Nat.sum_div_divisors q f
    _ = ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := rfl

set_option maxRecDepth 100000 in
theorem reduced_numerator_phase_sum_aux_period (x : ℝ) (m : ℕ) :
    FixedModelBoundsBlueprint.E (x + (m : ℝ)) = FixedModelBoundsBlueprint.E x := by
  unfold FixedModelBoundsBlueprint.E
  have harg : (((2 * Real.pi * (x + (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

set_option maxRecDepth 100000 in
theorem reduced_numerator_phase_sum_aux_cast (q n : ℕ) :
    (FixedModelBoundsBlueprint.R q n : ℂ) =
      ∑ d ∈ q.divisors, if d ∣ n then
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0 := by
  have h : (FixedModelBoundsBlueprint.R q n : ℂ) =
      ∑ d ∈ q.divisors.filter (fun d => d ∣ n),
        (((d : ℝ) * (ArithmeticFunction.moebius (q / d) : ℝ) : ℝ) : ℂ) := by
    unfold FixedModelBoundsBlueprint.R
    exact map_sum Complex.ofRealHom _ _
  rw [h, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hd : d ∣ n
  · simp only [hd, ite_true, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_intCast]
  · simp only [hd, ite_false]

set_option maxRecDepth 100000 in
theorem reduced_numerator_phase_sum (q n : ℕ) (hq : 0 < q) :
    (∑ a ∈ FixedModelBoundsBlueprint.A q,
      FixedModelBoundsBlueprint.E
        (-(n : ℝ) * ((a : ℝ) / q))) =
      (FixedModelBoundsBlueprint.R q n : ℂ) := by
  have hq1 : 1 ≤ q := hq
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq1R : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
  have ha : ∀ a : ℕ, FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q)) =
      FixedModelBoundsBlueprint.E ((((q - 1) * n : ℕ) : ℝ) * (a : ℝ) / q) := by
    intro a
    have hper := reduced_numerator_phase_sum_aux_period
      (-(n : ℝ) * ((a : ℝ) / q)) (a * n)
    have harg : -(n : ℝ) * ((a : ℝ) / q) + ((a * n : ℕ) : ℝ) =
        (((q - 1) * n : ℕ) : ℝ) * (a : ℝ) / q := by
      rw [Nat.cast_mul, Nat.cast_mul, hq1R]
      field_simp
      ring
    calc FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q)) =
        FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q) + ((a * n : ℕ) : ℝ)) :=
          hper.symm
      _ = FixedModelBoundsBlueprint.E ((((q - 1) * n : ℕ) : ℝ) * (a : ℝ) / q) := by
          rw [harg]
  have hsum : (∑ a ∈ FixedModelBoundsBlueprint.A q,
      FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q))) =
      ∑ a ∈ FixedModelBoundsBlueprint.A q,
        FixedModelBoundsBlueprint.E ((((q - 1) * n : ℕ) : ℝ) * (a : ℝ) / q) :=
    Finset.sum_congr rfl (fun a _ => ha a)
  rw [hsum, reduced_numerator_phase_sum_aux_divisor q ((q - 1) * n) hq,
    reduced_numerator_phase_sum_aux_cast]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hcop : Nat.Coprime d (q - 1) := by
    have h1 : Nat.Coprime (q - 1) q := by
      have h2 := (Nat.coprime_self_add_right (m := q - 1) (n := 1)).mpr
        (Nat.coprime_one_right (q - 1))
      rwa [Nat.sub_add_cancel hq1] at h2
    exact h1.symm.of_dvd_left hdq
  have hiff : d ∣ (q - 1) * n ↔ d ∣ n := hcop.dvd_mul_left
  by_cases hdn : d ∣ n
  · have h2 : d ∣ (q - 1) * n := hiff.mpr hdn
    simp only [h2, hdn, ite_true]
  · have h2 : ¬ (d ∣ (q - 1) * n) := fun hh => hdn (hiff.mp hh)
    simp only [h2, hdn, ite_false]

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_phase_add (x y : ℝ) :
    FixedModelBoundsBlueprint.E (x + y) =
      FixedModelBoundsBlueprint.E x * FixedModelBoundsBlueprint.E y := by
  unfold FixedModelBoundsBlueprint.E
  have harg : (((2 * Real.pi * (x + y) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_phase_period (x : ℝ) (m : ℕ) :
    FixedModelBoundsBlueprint.E (x + (m : ℝ)) = FixedModelBoundsBlueprint.E x := by
  unfold FixedModelBoundsBlueprint.E
  have harg : (((2 * Real.pi * (x + (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_complete (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ Finset.range m,
        FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) :
      FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold FixedModelBoundsBlueprint.E
    push_cast
    congr 1
    field_simp
  simp_rw [hpow]
  by_cases h : m ∣ a
  · simp [h, hz.mpr h]
  · simp only [h, ite_false]
    have hzm : z ^ m = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (m : ℂ) * (2 * Real.pi * Complex.I * a / m) =
          a * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [harg]
      exact Complex.exp_nat_mul_two_pi_mul_I a
    have hsum := geom_sum_mul z m
    rw [hzm, sub_self] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right
      (sub_ne_zero.mpr (fun hz1 => h (hz.mp hz1)))

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_coprime_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime b q then 1 else 0 := by
  have hg : Nat.gcd b q ≠ 0 := (Nat.gcd_pos_of_pos_right b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (Nat.gcd b q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff, and_comm]
  rw [← Finset.sum_filter, hs]
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (Nat.gcd b q)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_multiples (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (Finset.range q).filter (fun b => d ∣ b),
        FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← signed_model_normal_form_aux_complete m a hm]
  symm
  apply Finset.sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hj) hd),
        dvd_mul_right d j⟩
  · intro k hk
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr
      (by simpa [Nat.mul_comm] using Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hk).2
  · intro j _
    unfold FixedModelBoundsBlueprint.E
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_ramanujan_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ FixedModelBoundsBlueprint.A q,
        FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ Finset.range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) := by
      simp only [signed_model_normal_form_aux_coprime_indicator q _ hq,
        FixedModelBoundsBlueprint.A, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ Finset.range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← signed_model_normal_form_aux_multiples q a d hq
          (Nat.dvd_of_mem_divisors hd),
        Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_divisor_formula (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ FixedModelBoundsBlueprint.A q,
        FixedModelBoundsBlueprint.E ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := by
  rw [signed_model_normal_form_aux_ramanujan_sum q a hq]
  let f : ℕ → ℂ := fun d =>
    if d ∣ a then (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0
  calc
    (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0)) =
        ∑ d ∈ q.divisors, f (q / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hcomp : q / (q / d) = d :=
        Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq.ne'
      unfold f
      rw [hcomp]
      by_cases ha : q / d ∣ a <;> simp [ha]
      ring
    _ = ∑ d ∈ q.divisors, f d := Nat.sum_div_divisors q f
    _ = ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := rfl

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_phase_sum (q n : ℕ) (hq : 0 < q) :
    ∑ a ∈ FixedModelBoundsBlueprint.A q,
        FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q)) =
      ((FixedModelBoundsBlueprint.R q n : ℝ) : ℂ) := by
  have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hm : n * (q - 1) + n = n * q := by
    have h1 : n * (q - 1) + n = n * ((q - 1) + 1) := by ring
    rw [h1, hsub]
  have hmR : ((n * (q - 1) : ℕ) : ℝ) + (n : ℝ) = (n : ℝ) * (q : ℝ) := by
    have h2 := congrArg (fun k : ℕ => (k : ℝ)) hm
    push_cast at h2
    rw [Nat.cast_mul]
    exact h2
  have hconv : ∀ a : ℕ,
      FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q)) =
        FixedModelBoundsBlueprint.E (((n * (q - 1) : ℕ) : ℝ) * (a : ℝ) / q) := by
    intro a
    have hna : ((n * a : ℕ) : ℝ) = (n : ℝ) * (a : ℝ) := by push_cast; ring
    have harg : ((n * (q - 1) : ℕ) : ℝ) * (a : ℝ) / (q : ℝ) =
        -(n : ℝ) * ((a : ℝ) / q) + ((n * a : ℕ) : ℝ) := by
      rw [hna]
      field_simp
      linear_combination (a : ℝ) * hmR
    have hper := signed_model_normal_form_aux_phase_period
      (-(n : ℝ) * ((a : ℝ) / q)) (n * a)
    rw [harg]
    exact hper.symm
  have hdvd : ∀ d ∈ q.divisors, (d ∣ n * (q - 1) ↔ d ∣ n) := by
    intro d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hg2 : Nat.gcd d (q - 1) ∣ q - 1 := Nat.gcd_dvd_right d (q - 1)
    have hg3 : Nat.gcd d (q - 1) ∣ q := (Nat.gcd_dvd_left d (q - 1)).trans hdq
    have hg4 : Nat.gcd d (q - 1) ∣ 1 + (q - 1) := by
      rw [Nat.add_comm, hsub]
      exact hg3
    have hg5 : Nat.gcd d (q - 1) ∣ 1 :=
      (Nat.dvd_add_iff_left (k := Nat.gcd d (q - 1)) (m := 1) (n := q - 1) hg2).mpr hg4
    have hcop : Nat.Coprime d (q - 1) :=
      Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hg5)
    exact Nat.Coprime.dvd_mul_right hcop
  have hR : ((FixedModelBoundsBlueprint.R q n : ℝ) : ℂ) =
      ∑ d ∈ q.divisors,
        if d ∣ n then (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := by
    unfold FixedModelBoundsBlueprint.R
    rw [Finset.sum_filter, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : d ∣ n
    · simp only [if_pos h]
      push_cast
      ring
    · simp only [if_neg h]
      simp
  rw [Finset.sum_congr rfl (fun a _ => hconv a)]
  rw [signed_model_normal_form_aux_divisor_formula q (n * (q - 1)) hq]
  rw [hR]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ∣ n
  · have h2 : d ∣ n * (q - 1) := (hdvd d hd).mpr h
    simp [h, h2]
  · have h2 : ¬ (d ∣ n * (q - 1)) := fun hh => h ((hdvd d hd).mp hh)
    simp [h, h2]

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_coeff (q : ℕ) :
    (((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)) ^ 2 =
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) := by
  have h1 : ((ArithmeticFunction.moebius q : ℤ) : ℂ) =
      ((ArithmeticFunction.moebius q : ℝ) : ℂ) := by norm_cast
  have h2 : ((Nat.totient q : ℕ) : ℂ) = ((Nat.totient q : ℝ) : ℂ) := by norm_cast
  rw [h1, h2, ← Complex.ofReal_div, ← Complex.ofReal_pow, Complex.ofReal_inj]
  ring

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_re_add (z w : ℂ) : (z + w).re = z.re + w.re := rfl

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_re_sum (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ i ∈ s, (f i).re) = (∑ i ∈ s, f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
      signed_model_normal_form_aux_re_add]

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_integrand (n q a : ℕ) (β : ℝ) :
    (FixedModelBoundsBlueprint.M n q β) ^ 2 *
        FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q + β)) =
      ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) *
          FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q))) *
        ((FixedModelBoundsBlueprint.V n β) ^ 2 *
          FixedModelBoundsBlueprint.E (-(n : ℝ) * β)) := by
  have hc := signed_model_normal_form_aux_coeff q
  have hE : FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q + β)) =
      FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q)) *
        FixedModelBoundsBlueprint.E (-(n : ℝ) * β) := by
    have harg : -(n : ℝ) * ((a : ℝ) / q + β) =
        -(n : ℝ) * ((a : ℝ) / q) + (-(n : ℝ) * β) := by ring
    rw [harg, signed_model_normal_form_aux_phase_add]
  have hM : (FixedModelBoundsBlueprint.M n q β) ^ 2 =
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) *
        (FixedModelBoundsBlueprint.V n β) ^ 2 := by
    unfold FixedModelBoundsBlueprint.M
    rw [mul_pow, hc]
  rw [hM, hE]
  ring

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_integral (n q a : ℕ) :
    FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
        (fun β => (FixedModelBoundsBlueprint.M n q β) ^ 2 *
          FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q + β))) =
      ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) *
          FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q))) *
        FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
          (fun β => (FixedModelBoundsBlueprint.V n β) ^ 2 *
            FixedModelBoundsBlueprint.E (-(n : ℝ) * β)) := by
  have hfeq :
      (fun β => (FixedModelBoundsBlueprint.M n q β) ^ 2 *
          FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q + β))) =
      (fun β =>
        ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) *
            FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q))) *
          ((FixedModelBoundsBlueprint.V n β) ^ 2 *
            FixedModelBoundsBlueprint.E (-(n : ℝ) * β))) :=
    funext (signed_model_normal_form_aux_integrand n q a)
  unfold FixedModelBoundsBlueprint.J
  rw [hfeq, intervalIntegral.integral_const_mul]

set_option maxRecDepth 100000 in
theorem signed_model_normal_form_aux_q (n q : ℕ) (hq : 0 < q) :
    ∑ a ∈ FixedModelBoundsBlueprint.A q,
        (FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
          (fun β => (FixedModelBoundsBlueprint.M n q β) ^ 2 *
            FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q + β)))).re =
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) *
        FixedModelBoundsBlueprint.R q n *
        (FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
          (fun β => (FixedModelBoundsBlueprint.V n β) ^ 2 *
            FixedModelBoundsBlueprint.E (-(n : ℝ) * β))).re := by
  have hstep : ∀ a : ℕ,
      (FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
        (fun β => (FixedModelBoundsBlueprint.M n q β) ^ 2 *
          FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q + β)))).re =
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) *
        (FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q)) *
          FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
            (fun β => (FixedModelBoundsBlueprint.V n β) ^ 2 *
              FixedModelBoundsBlueprint.E (-(n : ℝ) * β))).re := by
    intro a
    rw [signed_model_normal_form_aux_integral n q a]
    have hrw :
        ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) *
            FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q))) *
          FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
            (fun β => (FixedModelBoundsBlueprint.V n β) ^ 2 *
              FixedModelBoundsBlueprint.E (-(n : ℝ) * β)) =
        (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 : ℝ) : ℂ) *
          (FixedModelBoundsBlueprint.E (-(n : ℝ) * ((a : ℝ) / q)) *
            FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
              (fun β => (FixedModelBoundsBlueprint.V n β) ^ 2 *
                FixedModelBoundsBlueprint.E (-(n : ℝ) * β))) := by ring
    rw [hrw, Complex.re_ofReal_mul]
  rw [Finset.sum_congr rfl (fun a _ => hstep a)]
  rw [← Finset.mul_sum, signed_model_normal_form_aux_re_sum, ← Finset.sum_mul,
    signed_model_normal_form_aux_phase_sum q n hq, Complex.re_ofReal_mul]
  ring

set_option maxRecDepth 100000 in
theorem signed_model_normal_form (n : ℕ) :
    FixedModelBoundsBlueprint.C n / (n : ℝ) =
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.signedCoeff q n *
          FixedModelBoundsBlueprint.S n q := by
  have hC : FixedModelBoundsBlueprint.C n =
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) *
          FixedModelBoundsBlueprint.R q n) *
        (FixedModelBoundsBlueprint.J (FixedModelBoundsBlueprint.H n q)
          (fun β => (FixedModelBoundsBlueprint.V n β) ^ 2 *
            FixedModelBoundsBlueprint.E (-(n : ℝ) * β))).re := by
    unfold FixedModelBoundsBlueprint.C
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : q ∈ Finset.Icc (1 : ℕ) 105 := hq
    have hq0 : 0 < q := by
      have h2 := (Finset.mem_Icc.mp hq').1
      omega
    exact signed_model_normal_form_aux_q n q hq0
  rw [hC, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  unfold FixedModelBoundsBlueprint.signedCoeff FixedModelBoundsBlueprint.S
  ring

set_option maxRecDepth 100000 in
theorem energy_model_normal_form_aux_card (q : ℕ) :
    ((FixedModelBoundsBlueprint.A q).card : ℝ) = (Nat.totient q : ℝ) := by
  have h : (FixedModelBoundsBlueprint.A q).card = Nat.totient q := by
    rw [FixedModelBoundsBlueprint.A, Nat.totient_eq_card_coprime]
    congr 1
    exact Finset.filter_congr fun a _ => Nat.coprime_comm
  exact_mod_cast h

set_option maxRecDepth 100000 in
theorem energy_model_normal_form_aux_norm (n q : ℕ) (β : ℝ) :
    ‖FixedModelBoundsBlueprint.M n q β‖ ^ 2 =
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
        ‖FixedModelBoundsBlueprint.V n β‖ ^ 2 := by
  simp only [FixedModelBoundsBlueprint.M, Complex.norm_mul, Complex.norm_div,
    Complex.norm_intCast, Complex.norm_natCast, mul_pow, div_pow, sq_abs]

set_option maxRecDepth 100000 in
theorem energy_model_normal_form_aux_integral (n q : ℕ) :
    FixedModelBoundsBlueprint.Jr (FixedModelBoundsBlueprint.H n q)
        (fun β => ‖FixedModelBoundsBlueprint.M n q β‖ ^ 2) =
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
        FixedModelBoundsBlueprint.Jr (FixedModelBoundsBlueprint.H n q)
          (fun β => ‖FixedModelBoundsBlueprint.V n β‖ ^ 2) := by
  have hfun :
      (fun β => ‖FixedModelBoundsBlueprint.M n q β‖ ^ 2) =
        fun β => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
          ‖FixedModelBoundsBlueprint.V n β‖ ^ 2 :=
    funext fun β => energy_model_normal_form_aux_norm n q β
  simp only [FixedModelBoundsBlueprint.Jr, hfun, intervalIntegral.integral_const_mul]

set_option maxRecDepth 100000 in
theorem energy_model_normal_form (n : ℕ) :
    FixedModelBoundsBlueprint.B n / (n : ℝ) =
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.energyCoeff q *
          FixedModelBoundsBlueprint.T n q := by
  have hφ : ∀ q ∈ FixedModelBoundsBlueprint.Q, (Nat.totient q : ℝ) ≠ 0 := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hpos : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
    exact_mod_cast hpos.ne'
  have hB : FixedModelBoundsBlueprint.B n =
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.energyCoeff q *
          FixedModelBoundsBlueprint.Jr (FixedModelBoundsBlueprint.H n q)
            (fun β => ‖FixedModelBoundsBlueprint.V n β‖ ^ 2) := by
    simp only [FixedModelBoundsBlueprint.B]
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq0 : (Nat.totient q : ℝ) ≠ 0 := hφ q hq
    rw [energy_model_normal_form_aux_card q, energy_model_normal_form_aux_integral]
    simp only [FixedModelBoundsBlueprint.energyCoeff]
    field_simp
  rw [hB, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro q _
  simp only [FixedModelBoundsBlueprint.T]
  ring

section

open MeasureTheory intervalIntegral
open scoped Interval

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_E_norm (x : ℝ) :
    ‖FixedModelBoundsBlueprint.E x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_E_add (x y : ℝ) :
    FixedModelBoundsBlueprint.E (x + y)
      = FixedModelBoundsBlueprint.E x * FixedModelBoundsBlueprint.E y := by
  simp only [FixedModelBoundsBlueprint.E, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_E_lip (x y : ℝ) :
    ‖FixedModelBoundsBlueprint.E x - FixedModelBoundsBlueprint.E y‖ ≤ 2 * Real.pi * |x - y| := by
  have h : FixedModelBoundsBlueprint.E x - FixedModelBoundsBlueprint.E y
      = (FixedModelBoundsBlueprint.E (x - y) - 1) * FixedModelBoundsBlueprint.E y := by
    rw [sub_mul, ← rescaled_kernel_bounds_aux_E_add, sub_add_cancel, one_mul]
  rw [h, norm_mul, rescaled_kernel_bounds_aux_E_norm, mul_one]
  unfold FixedModelBoundsBlueprint.E
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  rw [show 2 * Real.pi * (x - y) / 2 = Real.pi * (x - y) by ring]
  have hb : |Real.sin (Real.pi * (x - y))| ≤ |Real.pi * (x - y)| := Real.abs_sin_le_abs
  rw [abs_mul, abs_of_pos Real.pi_pos] at hb
  norm_num
  linarith

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_E_cont : Continuous FixedModelBoundsBlueprint.E := by
  unfold FixedModelBoundsBlueprint.E; fun_prop

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_V_cont (n : ℕ) :
    Continuous (FixedModelBoundsBlueprint.V n) := by
  unfold FixedModelBoundsBlueprint.V FixedModelBoundsBlueprint.E; fun_prop

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_tgt_cont :
    Continuous (fun t : ℝ =>
      FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ)) := by
  unfold FixedModelBoundsBlueprint.E; fun_prop

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_tgt_norm (t : ℝ) :
    ‖FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ)‖ ≤ 1 := by
  simpa [norm_mul, rescaled_kernel_bounds_aux_E_norm, Complex.norm_real, Real.norm_eq_abs] using
    Real.abs_sinc_le_one (Real.pi * t)

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_kernel_int (t : ℝ) :
    (∫ x in (0 : ℝ)..1, FixedModelBoundsBlueprint.E (x * t))
      = FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ) := by
  by_cases ht : t = 0
  · subst t; simp [FixedModelBoundsBlueprint.E, Real.sinc_zero]
  let a := Real.pi * t
  have ha : a ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
  let w := fun z : ℝ => Complex.exp ((z : ℂ) * Complex.I)
  have fac (x : ℝ) : FixedModelBoundsBlueprint.E (x * t)
      = FixedModelBoundsBlueprint.E (t / 2) * w ((2 * a) * x - a) := by
    simp only [FixedModelBoundsBlueprint.E, w, ← Complex.exp_add]
    congr 1
    dsimp [a]; push_cast; ring
  simp_rw [fac]
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1) w
    (show 2 * a ≠ 0 by positivity) (-a)
  simp only [mul_zero, zero_add, mul_one, show 2 * a + -a = a by ring] at h
  change _ * (∫ x in (0 : ℝ)..1, w (2 * a * x + -a)) = _
  rw [h]
  change FixedModelBoundsBlueprint.E (t / 2)
    * ((2 * a)⁻¹ • (∫ z in -a..a, Complex.exp ((z : ℂ) * Complex.I))) = _
  rw [integral_exp_mul_I_eq_sinc, Complex.real_smul]
  change FixedModelBoundsBlueprint.E (t / 2) * _
    = FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc a : ℂ)
  congr 1
  push_cast
  field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast ha]

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_range_poly (n : ℕ) (y : ℝ) :
    FixedModelBoundsBlueprint.V n y
      = ∑ k ∈ Finset.range n, FixedModelBoundsBlueprint.E (((k : ℝ) + 1) * y) := by
  unfold FixedModelBoundsBlueprint.V
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_cell (u : ℝ) (j : ℕ) :
    ‖FixedModelBoundsBlueprint.E (((j : ℝ) + 1) * u)
        - ∫ x in (j : ℝ)..((j : ℝ) + 1), FixedModelBoundsBlueprint.E (x * u)‖
      ≤ Real.pi * |u| := by
  let b : ℝ := j + 1
  let a : ℝ := j
  let g := fun x : ℝ => FixedModelBoundsBlueprint.E (x * u)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hg : Continuous g :=
    rescaled_kernel_bounds_aux_E_cont.comp (continuous_id.mul continuous_const)
  have he : (∫ _x in a..b, g b) = g b := by
    simp [intervalIntegral.integral_const, a, b]
  change ‖g b - ∫ x in a..b, g x‖ ≤ _
  rw [← he, ← intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]
  let C := 2 * Real.pi * |u|
  calc
    _ ≤ ∫ x in a..b, C * (b - x) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall ?_)
        ((show Continuous (fun x : ℝ => C * (b - x)) by fun_prop).intervalIntegrable _ _)
      intro x hx
      calc ‖g b - g x‖ ≤ 2 * Real.pi * |b * u - x * u| :=
              rescaled_kernel_bounds_aux_E_lip _ _
           _ = _ := by
              rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hx.2)]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
        integral_id, intervalIntegral.integral_const]
      dsimp [a, b, C]; ring

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_approx (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖FixedModelBoundsBlueprint.V n (t / (n : ℝ)) / (n : ℂ)
        - (FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ))‖
      ≤ Real.pi * |t| / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let u := t / (n : ℝ)
  let g := fun x : ℝ => FixedModelBoundsBlueprint.E (x * u)
  have hg : Continuous g :=
    rescaled_kernel_bounds_aux_E_cont.comp (continuous_id.mul continuous_const)
  have tel := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ)) (n := n)
    (fun k _ => hg.intervalIntegrable (μ := volume) (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ)))
  have integ : (∫ x in (0 : ℝ)..(n : ℝ), g x)
      = (n : ℂ) * (FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ)) := by
    have sm := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := (n : ℝ))
      (fun x : ℝ => FixedModelBoundsBlueprint.E (x * t)) hnR.ne'
    simp only [zero_div, div_self hnR.ne', rescaled_kernel_bounds_aux_kernel_int,
      Complex.real_smul, Complex.ofReal_natCast] at sm
    convert sm using 1
    apply intervalIntegral.integral_congr; intro x _
    unfold g u; congr 1; ring
  have C : ‖FixedModelBoundsBlueprint.V n u
        - (n : ℂ) * (FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ))‖
      ≤ (n : ℝ) * (Real.pi * |u|) := by
    rw [rescaled_kernel_bounds_aux_range_poly, ← integ]
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at tel
    rw [← tel, ← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans
      ((Finset.sum_le_sum (fun k _ => rescaled_kernel_bounds_aux_cell u k)).trans_eq (by simp))
  change ‖FixedModelBoundsBlueprint.V n u / (n : ℂ)
    - (FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ))‖ ≤ _
  rw [show FixedModelBoundsBlueprint.V n u / (n : ℂ)
      - (FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ))
      = (FixedModelBoundsBlueprint.V n u
        - (n : ℂ) * (FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ))) / (n : ℂ)
      by field_simp, norm_div, Complex.norm_natCast]
  rw [div_le_div_iff_of_pos_right hnR]
  apply C.trans_eq
  dsimp [u]; rw [abs_div, abs_of_pos hnR]; field_simp

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_avg_norm (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖FixedModelBoundsBlueprint.V n (t / (n : ℝ)) / (n : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast, div_le_one (by exact_mod_cast hn)]
  unfold FixedModelBoundsBlueprint.V
  exact (norm_sum_le _ _).trans
    (by simp [rescaled_kernel_bounds_aux_E_norm, Nat.card_Icc])

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_tgt_sq (t : ℝ) :
    (FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ)) ^ 2
        * FixedModelBoundsBlueprint.E (-t)
      = ((Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ) := by
  have h : FixedModelBoundsBlueprint.E (t / 2) * FixedModelBoundsBlueprint.E (t / 2)
      * FixedModelBoundsBlueprint.E (-t) = 1 := by
    rw [← rescaled_kernel_bounds_aux_E_add, ← rescaled_kernel_bounds_aux_E_add,
      show t / 2 + t / 2 + -t = 0 by ring]
    simp [FixedModelBoundsBlueprint.E]
  push_cast
  linear_combination ((Real.sinc (Real.pi * t) : ℂ) ^ 2) * h

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_scaled {𝕜 : Type*} [RCLike 𝕜] (v : ℝ → 𝕜) (d h : ℝ)
    (hd : d ≠ 0) :
    (∫ x in -h..h, v (x / d) / (d : 𝕜) ^ 2) = (∫ x in -(h / d)..h / d, v x) / (d : 𝕜) := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_div v hd, neg_div,
    RCLike.real_smul_eq_coe_mul]
  have hn : (d : 𝕜) ≠ 0 := by exact_mod_cast hd
  field_simp

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_int_bound {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ → 𝕜}
    (ha : Continuous a) (hb : Continuous b) (h C : ℝ) (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hab : ∀ x, ‖a x - b x‖ ≤ C * |x|) :
    ‖(∫ x in -h..h, a x) - (∫ x in -h..h, b x)‖ ≤ 2 * C * h ^ 2 := by
  rw [← intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _)]
  have step := intervalIntegral.norm_integral_le_of_norm_le_const (a := -h) (b := h) (C := C * h)
    (f := fun x => a x - b x) (fun x hx => (hab x).trans (mul_le_mul_of_nonneg_left (by
      rw [Set.uIoc_of_le (by linarith : -h ≤ h)] at hx
      exact abs_le.mpr ⟨hx.1.le, hx.2⟩) hC))
  exact step.trans_eq (by rw [abs_of_nonneg (by linarith : 0 ≤ h - -h)]; ring)

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds_aux_main (n : ℕ) (h : ℝ) (hn : 0 < n) (hh : 0 ≤ h) :
    |(FixedModelBoundsBlueprint.J (h / (n : ℝ))
        (fun β => (FixedModelBoundsBlueprint.V n β) ^ 2
          * FixedModelBoundsBlueprint.E (-(n : ℝ) * β))).re / (n : ℝ)
      - FixedModelBoundsBlueprint.Jr h (fun t => Real.sinc (Real.pi * t) ^ 2)|
        ≤ 4 * Real.pi * h ^ 2 / (n : ℝ) ∧
    |FixedModelBoundsBlueprint.Jr (h / (n : ℝ))
        (fun β => ‖FixedModelBoundsBlueprint.V n β‖ ^ 2) / (n : ℝ)
      - FixedModelBoundsBlueprint.Jr h (fun t => Real.sinc (Real.pi * t) ^ 2)|
        ≤ 4 * Real.pi * h ^ 2 / (n : ℝ) := by
  have hr : 0 < (n : ℝ) := by exact_mod_cast hn
  let FF := fun t : ℝ => FixedModelBoundsBlueprint.V n (t / (n : ℝ)) / (n : ℂ)
  let sqF := fun t : ℝ => (FF t) ^ 2 * FixedModelBoundsBlueprint.E (-t)
  let sqG := fun t : ℝ => (((Real.sinc (Real.pi * t)) ^ 2 : ℝ) : ℂ)
  let MM := fun t : ℝ => ‖FF t‖ ^ 2
  let JJ := fun t : ℝ => (Real.sinc (Real.pi * t)) ^ 2
  let tgt := fun t : ℝ =>
    FixedModelBoundsBlueprint.E (t / 2) * (Real.sinc (Real.pi * t) : ℂ)
  have cF : Continuous FF :=
    ((rescaled_kernel_bounds_aux_V_cont n).comp (continuous_id.div_const _)).div_const _
  have cSq : Continuous sqF :=
    (cF.pow 2).mul (rescaled_kernel_bounds_aux_E_cont.comp continuous_neg)
  have cJ : Continuous JJ := by dsimp [JJ]; fun_prop
  have cG : Continuous sqG := Complex.continuous_ofReal.comp cJ
  have cM : Continuous MM := cF.norm.pow 2
  have hp t : ‖FF t - tgt t‖ ≤ Real.pi * |t| / (n : ℝ) :=
    rescaled_kernel_bounds_aux_approx n hn t
  have hF t : ‖FF t‖ ≤ 1 := rescaled_kernel_bounds_aux_avg_norm n hn t
  have c : 0 ≤ 2 * Real.pi / (n : ℝ) := by positivity
  have pointC t : ‖sqF t - sqG t‖ ≤ 2 * Real.pi / (n : ℝ) * |t| := by
    change ‖FF t ^ 2 * FixedModelBoundsBlueprint.E (-t) - ((JJ t : ℝ) : ℂ)‖ ≤ _
    rw [show ((JJ t : ℝ) : ℂ) = tgt t ^ 2 * FixedModelBoundsBlueprint.E (-t) from
          (rescaled_kernel_bounds_aux_tgt_sq t).symm,
        ← sub_mul, norm_mul, rescaled_kernel_bounds_aux_E_norm, mul_one, sq_sub_sq, norm_mul]
    have hs : ‖FF t + tgt t‖ ≤ 2 :=
      (norm_add_le _ _).trans
        (by linarith [hF t, rescaled_kernel_bounds_aux_tgt_norm t])
    calc _ ≤ 2 * (Real.pi * |t| / (n : ℝ)) := by
            nlinarith [mul_le_mul hs (hp t) (norm_nonneg (FF t - tgt t))
              (by norm_num : (0 : ℝ) ≤ 2)]
         _ = _ := by ring
  have pointR t : ‖MM t - JJ t‖ ≤ 2 * Real.pi / (n : ℝ) * |t| := by
    have ht : ‖tgt t‖ ^ 2 = JJ t := by
      simp [tgt, JJ, norm_mul, rescaled_kernel_bounds_aux_E_norm, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    change ‖‖FF t‖ ^ 2 - JJ t‖ ≤ _
    rw [← ht, sq_sub_sq, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ ‖FF t‖ + ‖tgt t‖)]
    have hd := (abs_norm_sub_norm_le (FF t) (tgt t)).trans (hp t)
    have hs : ‖FF t‖ + ‖tgt t‖ ≤ 2 := by
      linarith [hF t, rescaled_kernel_bounds_aux_tgt_norm t]
    calc _ ≤ 2 * (Real.pi * |t| / (n : ℝ)) := by
            nlinarith [mul_le_mul hs hd (abs_nonneg (‖FF t‖ - ‖tgt t‖))
              (by norm_num : (0 : ℝ) ≤ 2)]
         _ = _ := by ring
  have sc : (∫ t in -h..h, sqF t)
      = (∫ β in -(h / (n : ℝ))..h / (n : ℝ),
          FixedModelBoundsBlueprint.V n β ^ 2
            * FixedModelBoundsBlueprint.E (-(n : ℝ) * β)) / (n : ℂ) := by
    convert rescaled_kernel_bounds_aux_scaled
      (fun β : ℝ => FixedModelBoundsBlueprint.V n β ^ 2
        * FixedModelBoundsBlueprint.E (-(n : ℝ) * β)) (n : ℝ) h hr.ne' using 1
    apply intervalIntegral.integral_congr
    intro t _
    have he : -(n : ℝ) * (t / (n : ℝ)) = -t := by field_simp
    change (FixedModelBoundsBlueprint.V n (t / (n : ℝ)) / (n : ℂ)) ^ 2
        * FixedModelBoundsBlueprint.E (-t)
      = (FixedModelBoundsBlueprint.V n (t / (n : ℝ)) ^ 2
        * FixedModelBoundsBlueprint.E (-(n : ℝ) * (t / (n : ℝ)))) / (((n : ℝ) : ℂ) ^ 2)
    rw [he, Complex.ofReal_natCast, div_pow]
    ring
  have sr : (∫ t in -h..h, MM t)
      = (∫ β in -(h / (n : ℝ))..h / (n : ℝ),
          ‖FixedModelBoundsBlueprint.V n β‖ ^ 2) / (n : ℝ) := by
    convert rescaled_kernel_bounds_aux_scaled
      (fun β : ℝ => ‖FixedModelBoundsBlueprint.V n β‖ ^ 2) (n : ℝ) h hr.ne' using 1
    apply intervalIntegral.integral_congr; intro t _
    simp [MM, FF, norm_div, Complex.norm_natCast, div_pow]
  have hG : (∫ t in -h..h, sqG t) = ((∫ t in -h..h, JJ t) : ℝ) :=
    intervalIntegral.integral_ofReal
  constructor
  · have hc := rescaled_kernel_bounds_aux_int_bound cSq cG h (2 * Real.pi / (n : ℝ)) hh c pointC
    have hl := (Complex.abs_re_le_norm _).trans hc
    rw [sc, hG, Complex.sub_re, Complex.ofReal_re] at hl
    have hre (z : ℂ) : (z / (n : ℂ)).re = z.re / (n : ℝ) := Complex.div_ofReal_re z (n : ℝ)
    rw [hre] at hl
    exact hl.trans_eq (by ring)
  · have hl := rescaled_kernel_bounds_aux_int_bound cM cJ h (2 * Real.pi / (n : ℝ)) hh c pointR
    rw [sr, Real.norm_eq_abs] at hl
    exact hl.trans_eq (by ring)

set_option maxRecDepth 100000 in
theorem rescaled_kernel_bounds (n q : ℕ) (hn : 0 < n) (hq : 1 ≤ q) :
    |FixedModelBoundsBlueprint.S n q -
        FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ))| ≤
        4 * Real.pi * ((105 : ℝ) / (q : ℝ)) ^ 2 / (n : ℝ) ∧
    |FixedModelBoundsBlueprint.T n q -
        FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ))| ≤
        4 * Real.pi * ((105 : ℝ) / (q : ℝ)) ^ 2 / (n : ℝ) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hh : 0 ≤ (105 : ℝ) / (q : ℝ) := by positivity
  have hH : FixedModelBoundsBlueprint.H n q = ((105 : ℝ) / (q : ℝ)) / (n : ℝ) := by
    simp only [FixedModelBoundsBlueprint.H]
    field_simp
  obtain ⟨h1, h2⟩ := rescaled_kernel_bounds_aux_main n ((105 : ℝ) / (q : ℝ)) hn hh
  simp only [FixedModelBoundsBlueprint.S, FixedModelBoundsBlueprint.T,
    FixedModelBoundsBlueprint.K, hH]
  exact ⟨h1, h2⟩

end

section

open MeasureTheory Real Complex Set Filter
open scoped FourierTransform Convolution Topology RealInnerProductSpace

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
def sinc_mass_bounds_aux_hset : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hset_mem_iff {t : ℝ} : t ∈ sinc_mass_bounds_aux_hset ↔ -(1 / 2 : ℝ) ≤ t ∧ t ≤ 1 / 2 := Iff.rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hset_meas : MeasurableSet sinc_mass_bounds_aux_hset := measurableSet_Icc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hset_neg_mem {t : ℝ} : -t ∈ sinc_mass_bounds_aux_hset ↔ t ∈ sinc_mass_bounds_aux_hset := by
  rw [sinc_mass_bounds_aux_hset_mem_iff, sinc_mass_bounds_aux_hset_mem_iff]
  constructor
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
def sinc_mass_bounds_aux_hind : ℝ → ℂ := sinc_mass_bounds_aux_hset.indicator (fun _ => 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hind_of_mem {t : ℝ} (ht : t ∈ sinc_mass_bounds_aux_hset) : sinc_mass_bounds_aux_hind t = 1 := by
  simp only [sinc_mass_bounds_aux_hind, Set.indicator_of_mem ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hind_of_notMem {t : ℝ} (ht : t ∉ sinc_mass_bounds_aux_hset) : sinc_mass_bounds_aux_hind t = 0 := by
  simp only [sinc_mass_bounds_aux_hind, Set.indicator_of_notMem ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hind_even (t : ℝ) : sinc_mass_bounds_aux_hind (-t) = sinc_mass_bounds_aux_hind t := by
  by_cases ht : t ∈ sinc_mass_bounds_aux_hset
  · rw [sinc_mass_bounds_aux_hind_of_mem (sinc_mass_bounds_aux_hset_neg_mem.mpr ht), sinc_mass_bounds_aux_hind_of_mem ht]
  · rw [sinc_mass_bounds_aux_hind_of_notMem (fun h => ht (sinc_mass_bounds_aux_hset_neg_mem.mp h)), sinc_mass_bounds_aux_hind_of_notMem ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hind_mul_self (t : ℝ) : sinc_mass_bounds_aux_hind t * sinc_mass_bounds_aux_hind t = sinc_mass_bounds_aux_hind t := by
  by_cases ht : t ∈ sinc_mass_bounds_aux_hset
  · rw [sinc_mass_bounds_aux_hind_of_mem ht, one_mul]
  · rw [sinc_mass_bounds_aux_hind_of_notMem ht, mul_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hset_measure_ne_top : volume sinc_mass_bounds_aux_hset ≠ ⊤ := by
  have h : volume sinc_mass_bounds_aux_hset < ⊤ := isCompact_Icc.measure_lt_top
  exact h.ne

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hind_integrable : Integrable sinc_mass_bounds_aux_hind := by
  rw [sinc_mass_bounds_aux_hind, integrable_indicator_iff sinc_mass_bounds_aux_hset_meas]
  exact integrableOn_const sinc_mass_bounds_aux_hset_measure_ne_top

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_integral_hind : ∫ t : ℝ, sinc_mass_bounds_aux_hind t = 1 := by
  have h1 : (∫ t : ℝ, sinc_mass_bounds_aux_hind t) = volume.real sinc_mass_bounds_aux_hset • (1 : ℂ) := by
    rw [sinc_mass_bounds_aux_hind, integral_indicator_const (1 : ℂ) sinc_mass_bounds_aux_hset_meas]
  rw [h1]
  have h2 : volume.real sinc_mass_bounds_aux_hset = 1 := by
    show volume.real (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) = 1
    rw [Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
  rw [h2]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hind_ft (w : ℝ) : 𝓕 sinc_mass_bounds_aux_hind w = ((Real.sinc (Real.pi * w) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  simp only [Real.inner_apply]
  have hpt : ∀ v : ℝ, Complex.exp ((↑(-2 * Real.pi * (v * w)) : ℂ) * Complex.I) • sinc_mass_bounds_aux_hind v
      = sinc_mass_bounds_aux_hset.indicator
          (fun v : ℝ => Complex.exp ((↑(-2 * Real.pi * (v * w)) : ℂ) * Complex.I)) v := by
    intro v
    by_cases hv : v ∈ sinc_mass_bounds_aux_hset
    · rw [sinc_mass_bounds_aux_hind_of_mem hv, Set.indicator_of_mem hv, smul_eq_mul, mul_one]
    · rw [sinc_mass_bounds_aux_hind_of_notMem hv, Set.indicator_of_notMem hv, smul_zero]
  simp_rw [hpt]
  rw [MeasureTheory.integral_indicator sinc_mass_bounds_aux_hset_meas]
  simp only [sinc_mass_bounds_aux_hset]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hrw : ∀ x : ℝ, (-2 * Real.pi * (x * w)) = ((-2 * Real.pi * w) * x) := by
    intro x
    ring
  have hrw' : ∀ x : ℝ, (↑(-2 * Real.pi * (x * w)) : ℂ) = ↑((-2 * Real.pi * w) * x) := by
    intro x
    rw [hrw x]
  simp_rw [hrw']
  by_cases hw : w = 0
  · subst hw
    have hc0 : (fun x : ℝ => Complex.exp ((↑((-2 * Real.pi * 0) * x) : ℂ) * Complex.I))
        = fun _ => (1 : ℂ) := by
      funext x
      simp
    rw [hc0, intervalIntegral.integral_const]
    simp [Real.sinc_zero]
    norm_num
  · have hne : (-2 * Real.pi * w) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) Real.pi_ne_zero) hw
    have hstep : (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          Complex.exp ((↑((-2 * Real.pi * w) * x) : ℂ) * Complex.I))
        = (-2 * Real.pi * w)⁻¹ • ∫ t in ((-2 * Real.pi * w) * (-(1 / 2 : ℝ)))..((-2 * Real.pi * w) * (1 / 2)),
            Complex.exp ((↑t : ℂ) * Complex.I) :=
      intervalIntegral.integral_comp_mul_left
        (fun t : ℝ => Complex.exp ((↑t : ℂ) * Complex.I)) hne
    rw [hstep]
    have e1 : (-2 * Real.pi * w) * (-(1 / 2 : ℝ)) = Real.pi * w := by ring
    have e2 : (-2 * Real.pi * w) * (1 / 2 : ℝ) = -(Real.pi * w) := by ring
    rw [e1, e2, intervalIntegral.integral_symm, integral_exp_mul_I_eq_sinc]
    rw [Complex.real_smul]
    have hkey : ((-2 * Real.pi * w)⁻¹ * -(2 * (Real.pi * w) * Real.sinc (Real.pi * w)) : ℝ)
        = Real.sinc (Real.pi * w) := by
      field_simp [hne] <;> ring
    calc _ = ((↑((-2 * Real.pi * w)⁻¹
            * -(2 * (Real.pi * w) * Real.sinc (Real.pi * w))) : ℂ)) := by
          push_cast <;> ring
      _ = _ := by rw [hkey]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_hind_eventuallyEq (s : ℝ) (h1 : s ≠ -(1 / 2 : ℝ)) (h2 : s ≠ (1 / 2 : ℝ)) :
    ∀ᶠ y in 𝓝 s, sinc_mass_bounds_aux_hind y = sinc_mass_bounds_aux_hind s := by
  by_cases hs1 : (-(1 / 2 : ℝ)) < s
  · by_cases hs2 : s < (1 / 2 : ℝ)
    · have hm : s ∈ sinc_mass_bounds_aux_hset := sinc_mass_bounds_aux_hset_mem_iff.mpr ⟨le_of_lt hs1, le_of_lt hs2⟩
      filter_upwards [Ioo_mem_nhds hs1 hs2] with y hy
      have hy' := Set.mem_Ioo.mp hy
      rw [sinc_mass_bounds_aux_hind_of_mem (sinc_mass_bounds_aux_hset_mem_iff.mpr ⟨le_of_lt hy'.1, le_of_lt hy'.2⟩), sinc_mass_bounds_aux_hind_of_mem hm]
    · have hs2' : (1 / 2 : ℝ) < s := lt_of_le_of_ne (le_of_not_gt hs2) (fun hcon => h2 hcon.symm)
      have hm : s ∉ sinc_mass_bounds_aux_hset :=
        fun hx => absurd (sinc_mass_bounds_aux_hset_mem_iff.mp hx).2 (by linarith : ¬ (s ≤ 1 / 2))
      filter_upwards [Ioi_mem_nhds hs2'] with y hy
      have hy' := Set.mem_Ioi.mp hy
      rw [sinc_mass_bounds_aux_hind_of_notMem
          (fun hx => absurd (sinc_mass_bounds_aux_hset_mem_iff.mp hx).2 (by linarith : ¬ (y ≤ 1 / 2))),
        sinc_mass_bounds_aux_hind_of_notMem hm]
  · have hs1' : s < -(1 / 2 : ℝ) := lt_of_le_of_ne (le_of_not_gt hs1) h1
    have hm : s ∉ sinc_mass_bounds_aux_hset :=
      fun hx => absurd (sinc_mass_bounds_aux_hset_mem_iff.mp hx).1 (by linarith : ¬ (-(1 / 2 : ℝ) ≤ s))
    filter_upwards [Iio_mem_nhds hs1'] with y hy
    have hy' := Set.mem_Iio.mp hy
    rw [sinc_mass_bounds_aux_hind_of_notMem
        (fun hx => absurd (sinc_mass_bounds_aux_hset_mem_iff.mp hx).1 (by linarith : ¬ (-(1 / 2 : ℝ) ≤ y))),
      sinc_mass_bounds_aux_hind_of_notMem hm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_convolution_hind_continuousAt_zero :
    ContinuousAt (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind) 0 := by
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun t => sinc_mass_bounds_aux_hind t * sinc_mass_bounds_aux_hind (x - t)) volume := by
    intro x
    simpa using (sinc_mass_bounds_aux_hind_integrable.aestronglyMeasurable.convolution_integrand_snd
      (ContinuousLinearMap.mul ℂ ℂ) sinc_mass_bounds_aux_hind_integrable.aestronglyMeasurable x)
  have hbound : ∀ x t : ℝ, ‖sinc_mass_bounds_aux_hind t * sinc_mass_bounds_aux_hind (x - t)‖ ≤ ‖sinc_mass_bounds_aux_hind t‖ := by
    intro x t
    have h3 : ‖sinc_mass_bounds_aux_hind (x - t)‖ ≤ 1 := by
      by_cases hmem : (x - t) ∈ sinc_mass_bounds_aux_hset
      · rw [sinc_mass_bounds_aux_hind_of_mem hmem]
        simp
      · rw [sinc_mass_bounds_aux_hind_of_notMem hmem]
        simp
    rw [norm_mul]
    calc ‖sinc_mass_bounds_aux_hind t‖ * ‖sinc_mass_bounds_aux_hind (x - t)‖ ≤ ‖sinc_mass_bounds_aux_hind t‖ * 1 :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ‖sinc_mass_bounds_aux_hind t‖ := mul_one _
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun x => sinc_mass_bounds_aux_hind t * sinc_mass_bounds_aux_hind (x - t)) (𝓝 (0 : ℝ))
      (𝓝 (sinc_mass_bounds_aux_hind t * sinc_mass_bounds_aux_hind (-t))) := by
    filter_upwards [MeasureTheory.volume.ae_ne (-(1 / 2 : ℝ)),
      MeasureTheory.volume.ae_ne (1 / 2 : ℝ)] with t h1 h2
    have hsub : Tendsto (fun x : ℝ => x - t) (𝓝 (0 : ℝ)) (𝓝 (-t)) := by
      have hc : ContinuousAt (fun x : ℝ => x - t) 0 := by fun_prop
      simpa using hc.tendsto
    have hkey : ∀ᶠ y in 𝓝 (-t), sinc_mass_bounds_aux_hind y = sinc_mass_bounds_aux_hind (-t) :=
      sinc_mass_bounds_aux_hind_eventuallyEq (-t) (fun hcon => h2 (by linarith)) (fun hcon => h1 (by linarith))
    have hconv : Tendsto (fun x : ℝ => sinc_mass_bounds_aux_hind (x - t)) (𝓝 (0 : ℝ)) (𝓝 (sinc_mass_bounds_aux_hind (-t))) := by
      refine (tendsto_const_nhds.congr' ?_)
      filter_upwards [hsub.eventually hkey] with x hx
      exact hx.symm
    exact tendsto_const_nhds.mul hconv
  have hmain : Tendsto (fun x : ℝ => ∫ t, sinc_mass_bounds_aux_hind t * sinc_mass_bounds_aux_hind (x - t)) (𝓝 (0 : ℝ))
      (𝓝 (∫ t, sinc_mass_bounds_aux_hind t * sinc_mass_bounds_aux_hind (-t))) :=
    tendsto_integral_filter_of_dominated_convergence (fun t => ‖sinc_mass_bounds_aux_hind t‖)
      (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall (hbound x))
      sinc_mass_bounds_aux_hind_integrable.norm hlim
  have hout : Tendsto (fun x : ℝ => (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind) x) (𝓝 (0 : ℝ))
      (𝓝 ((sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind) 0)) := by
    simpa only [convolution_mul, zero_sub] using hmain
  exact hout

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_sinc_sq_nonneg (t : ℝ) : 0 ≤ Real.sinc (Real.pi * t) ^ 2 := sq_nonneg _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_sinc_sq_le_one (t : ℝ) : Real.sinc (Real.pi * t) ^ 2 ≤ 1 := by
  have hA := Real.sinc_le_one (Real.pi * t)
  have hB := Real.neg_one_le_sinc (Real.pi * t)
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_sinc_sq_even (t : ℝ) :
    Real.sinc (Real.pi * (-t)) ^ 2 = Real.sinc (Real.pi * t) ^ 2 := by
  rw [mul_neg, Real.sinc_neg]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_sinc_sq_le (t : ℝ) (ht : t ≠ 0) :
    Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := by
  have hpi : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
  rw [Real.sinc_of_ne_zero hpi]
  have h1 : Real.sin (Real.pi * t) ^ 2 ≤ 1 := by
    have hA := Real.sin_le_one (Real.pi * t)
    have hB := Real.neg_one_le_sin (Real.pi * t)
    nlinarith
  have h2 : (0 : ℝ) < Real.pi ^ 2 * t ^ 2 := by positivity
  have h3 : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
  calc (Real.sin (Real.pi * t) / (Real.pi * t)) ^ 2
      = Real.sin (Real.pi * t) ^ 2 / (Real.pi ^ 2 * t ^ 2) := by rw [div_pow, h3]
    _ ≤ 1 / (Real.pi ^ 2 * t ^ 2) := div_le_div_of_nonneg_right h1 h2.le

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_sinc_sq_le_inv (t : ℝ) (ht : t ≠ 0) :
    Real.sinc (Real.pi * t) ^ 2 ≤ (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ := by
  calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := sinc_mass_bounds_aux_sinc_sq_le t ht
    _ = (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ := by rw [div_eq_mul_inv, one_mul, mul_inv_rev]; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_sinc_sq_le_two (t : ℝ) :
    Real.sinc (Real.pi * t) ^ 2 ≤ 2 / (1 + (Real.pi * t) ^ 2) := by
  have hrw : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
  have hden : (0 : ℝ) < 1 + Real.pi ^ 2 * t ^ 2 := by positivity
  by_cases ht : t = 0
  · subst ht
    norm_num [Real.sinc_zero]
  · have hu0 : (0 : ℝ) < Real.pi ^ 2 * t ^ 2 := by positivity
    rcases le_or_gt (Real.pi ^ 2 * t ^ 2) 1 with h | h
    · have h2 : (1 : ℝ) ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := by
        rw [le_div_iff₀ hden]
        linarith
      calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 := sinc_mass_bounds_aux_sinc_sq_le_one t
        _ ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := h2
        _ = 2 / (1 + (Real.pi * t) ^ 2) := by rw [hrw]
    · have h3 : 1 / (Real.pi ^ 2 * t ^ 2) ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := by
        rw [div_le_div_iff₀ hu0 hden]
        nlinarith
      calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := sinc_mass_bounds_aux_sinc_sq_le t ht
        _ ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := h3
        _ = 2 / (1 + (Real.pi * t) ^ 2) := by rw [hrw]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_sinc_sq_integrable : Integrable (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) := by
    fun_prop
  have hG : Integrable (fun t : ℝ => 2 / (1 + (Real.pi * t) ^ 2)) := by
    have h2 : Integrable (fun x : ℝ => 2 * (1 + x ^ 2) ⁻¹) :=
      integrable_inv_one_add_sq.const_mul 2
    have h3 : Integrable (fun t : ℝ => 2 * (1 + (Real.pi * t) ^ 2) ⁻¹) :=
      h2.comp_mul_left' Real.pi_ne_zero
    refine h3.congr (ae_of_all _ fun t => ?_)
    simp only [div_eq_mul_inv]
  refine Integrable.mono' hG hcont.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sinc_mass_bounds_aux_sinc_sq_nonneg t)]
  exact sinc_mass_bounds_aux_sinc_sq_le_two t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_sinc_sq_total : ∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 = 1 := by
  have hT_int : Integrable (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind) :=
    sinc_mass_bounds_aux_hind_integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) sinc_mass_bounds_aux_hind_integrable
  have hFT : ∀ ξ : ℝ, 𝓕 (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind) ξ
      = ((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ) := by
    intro ξ
    rw [Real.fourier_mul_convolution_eq sinc_mass_bounds_aux_hind_integrable sinc_mass_bounds_aux_hind_integrable ξ, sinc_mass_bounds_aux_hind_ft ξ]
    push_cast
    ring
  have hFT_int : Integrable (𝓕 (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind)) := by
    have h1 : Integrable (fun ξ : ℝ => ((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ)) :=
      Integrable.iff_ofReal.mp sinc_mass_bounds_aux_sinc_sq_integrable
    exact h1.congr (ae_of_all _ fun ξ => (hFT ξ).symm)
  have hinv : 𝓕⁻ (𝓕 (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind)) 0
      = (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind) 0 :=
    hT_int.fourierInv_fourier_eq hFT_int sinc_mass_bounds_aux_convolution_hind_continuousAt_zero
  have hT0 : (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind) 0 = 1 := by
    rw [convolution_mul]
    simp only [zero_sub]
    have hself : ∀ t : ℝ, sinc_mass_bounds_aux_hind t * sinc_mass_bounds_aux_hind (-t) = sinc_mass_bounds_aux_hind t := by
      intro t
      rw [sinc_mass_bounds_aux_hind_even t]
      exact sinc_mass_bounds_aux_hind_mul_self t
    simp_rw [hself]
    exact sinc_mass_bounds_aux_integral_hind
  have hF0 : 𝓕⁻ (𝓕 (sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] sinc_mass_bounds_aux_hind)) 0
      = ((∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ) := by
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    rw [integral_congr_ae (ae_of_all _ fun v => hFT v)]
    first
      | exact integral_ofReal
      | norm_cast
  have hfin : ((∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hF0, hinv, hT0]
  exact Complex.ofReal_inj.mp hfin

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma sinc_mass_bounds_aux_trunc_bound (f : ℝ → ℝ) (hf_nonneg : ∀ t, 0 ≤ f t) (hf_even : ∀ t, f (-t) = f t)
    (hf_bound : ∀ t, t ≠ 0 → f t ≤ (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹)
    (hf_int : Integrable f) (hf_tot : ∫ t : ℝ, f t = 1) (h : ℝ) (hh : 0 < h) :
    let k := intervalIntegral (fun t : ℝ => f t) (-h) h MeasureTheory.volume
    0 ≤ k ∧ k ≤ 1 ∧ 1 - 2 / (9 * h) ≤ k := by
  dsimp only
  have hle : -h ≤ h := by linarith
  have hk : intervalIntegral (fun t : ℝ => f t) (-h) h volume
      = ∫ t in Ioc (-h) h, f t ∂volume := intervalIntegral.integral_of_le hle
  have hbound_int : IntegrableOn (fun t : ℝ => (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹) (Ioi h) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi h) :=
      integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := h) (by norm_num) hh
    have hmul : IntegrableOn (fun t : ℝ => (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ)) (Ioi h) :=
      hbase.const_mul _
    refine hmul.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have htpos : 0 < t := hh.trans ht
    show (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ) = (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg htpos.le, Real.rpow_two]
  have htail : ∫ t in Ioi h, f t ∂volume ≤ (Real.pi ^ 2)⁻¹ * h⁻¹ := by
    have hA : ∫ t in Ioi h, f t ∂volume ≤ ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume :=
      setIntegral_mono_on hf_int.integrableOn hbound_int measurableSet_Ioi
        (fun t ht => hf_bound t (ne_of_gt (lt_of_lt_of_le hh ht.le)))
    have hB : ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume = (Real.pi ^ 2)⁻¹ * h⁻¹ := by
      have hc : ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume
          = ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ) ∂volume := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        have htpos : 0 < t := hh.trans ht
        show (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ = (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ)
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg htpos.le, Real.rpow_two]
      rw [hc, integral_const_mul, integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hh]
      have h3 : (-h ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1)) = h⁻¹ := by
        rw [show (-2 : ℝ) + 1 = -1 by ring, Real.rpow_neg_one]
        simp
      rw [h3]
    linarith [hA, hB]
  have hleft : ∫ t in Iic (-h), f t ∂volume = ∫ t in Ioi h, f t ∂volume := by
    have h1 : ∫ t in Iic (-h), f t ∂volume = ∫ t in Iic (-h), f (-t) ∂volume :=
      setIntegral_congr_fun measurableSet_Iic (fun x _ => (hf_even x).symm)
    rw [h1, integral_comp_neg_Iic (-h) f]
    simp
  have hpi : (9 : ℝ) < Real.pi ^ 2 := by
    have h4 := Real.pi_gt_three
    nlinarith
  have hinv : (Real.pi ^ 2)⁻¹ ≤ (9 : ℝ)⁻¹ := by
    have h5 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) hpi.le
    simpa using h5
  have htail' : ∫ t in Ioi h, f t ∂volume ≤ (9 : ℝ)⁻¹ * h⁻¹ := by
    have h6 := mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr hh.le)
    linarith [htail, h6]
  have hcomp : ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume
      = ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume := by
    rw [compl_Ioc]
    exact setIntegral_union (Iic_disjoint_Ioi hle) measurableSet_Ioi hf_int.integrableOn
      hf_int.integrableOn
  have htotal : (∫ t in Ioc (-h) h, f t ∂volume) + ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume = 1 := by
    rw [integral_add_compl measurableSet_Ioc hf_int]
    exact hf_tot
  have hnn : 0 ≤ ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume :=
    setIntegral_nonneg measurableSet_Ioc.compl (fun u _ => hf_nonneg u)
  have htail2 : ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume ≤ 2 / (9 * h) := by
    have hA : ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume ≤ 2 * ((9 : ℝ)⁻¹ * h⁻¹) := by
      rw [hleft]
      linarith [htail']
    have hB : 2 * ((9 : ℝ)⁻¹ * h⁻¹) = 2 / (9 * h) := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ring
    linarith [hA, hB]
  refine ⟨?_, ?_, ?_⟩
  · exact intervalIntegral.integral_nonneg hle (fun u _ => hf_nonneg u)
  · rw [hk]
    linarith [htotal, hnn]
  · rw [hk]
    rw [hcomp] at htotal
    linarith [htotal, htail2]

end

set_option maxRecDepth 100000 in
theorem sinc_mass_bounds (h : ℝ) (hh : 0 < h) :
    0 ≤ FixedModelBoundsBlueprint.K h ∧
      FixedModelBoundsBlueprint.K h ≤ 1 ∧
      1 - 2 / (9 * h) ≤ FixedModelBoundsBlueprint.K h := by
  have hmain := sinc_mass_bounds_aux_trunc_bound
    (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2)
    sinc_mass_bounds_aux_sinc_sq_nonneg
    sinc_mass_bounds_aux_sinc_sq_even
    sinc_mass_bounds_aux_sinc_sq_le_inv
    sinc_mass_bounds_aux_sinc_sq_integrable
    sinc_mass_bounds_aux_sinc_sq_total h hh
  simpa [FixedModelBoundsBlueprint.K, FixedModelBoundsBlueprint.Jr] using hmain

set_option maxRecDepth 100000 in
def signed_kernel_table_aux_ram (q t : ℕ) : ℤ :=
  ∑ d ∈ q.divisors.filter (fun d => d ∣ t), (d : ℤ) * ArithmeticFunction.moebius (q/d)
set_option maxRecDepth 100000 in
def signed_kernel_table_aux_coef (q t : ℕ) : ℚ :=
  (ArithmeticFunction.moebius q : ℚ)^2 / (q.totient : ℚ)^2 * (signed_kernel_table_aux_ram q t : ℚ)
set_option maxRecDepth 100000 in
def signed_kernel_table_aux_leftEnd (q : ℕ) : ℚ := if q ∣ 30 then 1 - 2*(q : ℚ)/(9*105) else 0
set_option maxRecDepth 100000 in
def signed_kernel_table_aux_table : List ℤ := [0, 997883, 995767, 496825, 0, 247354, 493650, -27778, 0, 0, 244708, -10000, 0, -6945, -27778, 121031, 0, -3907, 0, -3087, 0, -13889, -10000, -2067, 0, 0, -6945, 0, 0, -1276, 117063, -1112, 0, -5000, -3907, -6945, 0, -772, -3087, -3473, 0, -625, -13889, -567, 0, 0, -2067, -473, 0, 0, 0, -1954, 0, -370, 0, -2500, 0, -1544, -1276, -298, 0, -278, -1112, 0, 0, -1737, -5000, -230, 0, -1034, -6945, -205, 0, -193, -772, 0, 0, -2778, -3473, -165, 0, 0, -625, -149, 0, -977, -567, -638, 0, -130, 0, -2315, 0, -556, -473, -772, 0, -109, 0, 0, 0, -100, -1954, -97, 0, -3473]
set_option maxRecDepth 100000 in
def signed_kernel_table_aux_minorant (q : ℕ) : ℚ := (signed_kernel_table_aux_table.getD q 0 : ℚ) / 1000000
set_option maxRecDepth 100000 in
def signed_kernel_table_aux_Certified (q : ℕ) : Prop := ∀ t ∈ q.divisors, q.gcd 30 ∣ t →
  signed_kernel_table_aux_minorant q ≤ signed_kernel_table_aux_coef q t * signed_kernel_table_aux_leftEnd q ∧ signed_kernel_table_aux_minorant q ≤ signed_kernel_table_aux_coef q t
set_option maxRecDepth 100000 in
instance signed_kernel_table_aux_decCert (q : ℕ) : Decidable (signed_kernel_table_aux_Certified q) := inferInstanceAs (Decidable (∀ t ∈ q.divisors, q.gcd 30 ∣ t →
  signed_kernel_table_aux_minorant q ≤ signed_kernel_table_aux_coef q t * signed_kernel_table_aux_leftEnd q ∧ signed_kernel_table_aux_minorant q ≤ signed_kernel_table_aux_coef q t))
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert1 : signed_kernel_table_aux_Certified 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert2 : signed_kernel_table_aux_Certified 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert3 : signed_kernel_table_aux_Certified 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert4 : signed_kernel_table_aux_Certified 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert5 : signed_kernel_table_aux_Certified 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert6 : signed_kernel_table_aux_Certified 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert7 : signed_kernel_table_aux_Certified 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert8 : signed_kernel_table_aux_Certified 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert9 : signed_kernel_table_aux_Certified 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert10 : signed_kernel_table_aux_Certified 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert11 : signed_kernel_table_aux_Certified 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert12 : signed_kernel_table_aux_Certified 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert13 : signed_kernel_table_aux_Certified 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert14 : signed_kernel_table_aux_Certified 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert15 : signed_kernel_table_aux_Certified 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert16 : signed_kernel_table_aux_Certified 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert17 : signed_kernel_table_aux_Certified 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert18 : signed_kernel_table_aux_Certified 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert19 : signed_kernel_table_aux_Certified 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert20 : signed_kernel_table_aux_Certified 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert21 : signed_kernel_table_aux_Certified 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert22 : signed_kernel_table_aux_Certified 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert23 : signed_kernel_table_aux_Certified 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert24 : signed_kernel_table_aux_Certified 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert25 : signed_kernel_table_aux_Certified 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert26 : signed_kernel_table_aux_Certified 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert27 : signed_kernel_table_aux_Certified 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert28 : signed_kernel_table_aux_Certified 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert29 : signed_kernel_table_aux_Certified 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert30 : signed_kernel_table_aux_Certified 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert31 : signed_kernel_table_aux_Certified 31 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert32 : signed_kernel_table_aux_Certified 32 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert33 : signed_kernel_table_aux_Certified 33 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert34 : signed_kernel_table_aux_Certified 34 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert35 : signed_kernel_table_aux_Certified 35 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert36 : signed_kernel_table_aux_Certified 36 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert37 : signed_kernel_table_aux_Certified 37 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert38 : signed_kernel_table_aux_Certified 38 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert39 : signed_kernel_table_aux_Certified 39 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert40 : signed_kernel_table_aux_Certified 40 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert41 : signed_kernel_table_aux_Certified 41 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert42 : signed_kernel_table_aux_Certified 42 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert43 : signed_kernel_table_aux_Certified 43 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert44 : signed_kernel_table_aux_Certified 44 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert45 : signed_kernel_table_aux_Certified 45 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert46 : signed_kernel_table_aux_Certified 46 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert47 : signed_kernel_table_aux_Certified 47 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert48 : signed_kernel_table_aux_Certified 48 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert49 : signed_kernel_table_aux_Certified 49 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert50 : signed_kernel_table_aux_Certified 50 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert51 : signed_kernel_table_aux_Certified 51 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert52 : signed_kernel_table_aux_Certified 52 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert53 : signed_kernel_table_aux_Certified 53 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert54 : signed_kernel_table_aux_Certified 54 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert55 : signed_kernel_table_aux_Certified 55 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert56 : signed_kernel_table_aux_Certified 56 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert57 : signed_kernel_table_aux_Certified 57 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert58 : signed_kernel_table_aux_Certified 58 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert59 : signed_kernel_table_aux_Certified 59 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert60 : signed_kernel_table_aux_Certified 60 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert61 : signed_kernel_table_aux_Certified 61 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert62 : signed_kernel_table_aux_Certified 62 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert63 : signed_kernel_table_aux_Certified 63 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert64 : signed_kernel_table_aux_Certified 64 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert65 : signed_kernel_table_aux_Certified 65 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert66 : signed_kernel_table_aux_Certified 66 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert67 : signed_kernel_table_aux_Certified 67 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert68 : signed_kernel_table_aux_Certified 68 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert69 : signed_kernel_table_aux_Certified 69 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert70 : signed_kernel_table_aux_Certified 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert71 : signed_kernel_table_aux_Certified 71 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert72 : signed_kernel_table_aux_Certified 72 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert73 : signed_kernel_table_aux_Certified 73 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert74 : signed_kernel_table_aux_Certified 74 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert75 : signed_kernel_table_aux_Certified 75 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert76 : signed_kernel_table_aux_Certified 76 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert77 : signed_kernel_table_aux_Certified 77 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert78 : signed_kernel_table_aux_Certified 78 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert79 : signed_kernel_table_aux_Certified 79 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert80 : signed_kernel_table_aux_Certified 80 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert81 : signed_kernel_table_aux_Certified 81 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert82 : signed_kernel_table_aux_Certified 82 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert83 : signed_kernel_table_aux_Certified 83 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert84 : signed_kernel_table_aux_Certified 84 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert85 : signed_kernel_table_aux_Certified 85 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert86 : signed_kernel_table_aux_Certified 86 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert87 : signed_kernel_table_aux_Certified 87 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert88 : signed_kernel_table_aux_Certified 88 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert89 : signed_kernel_table_aux_Certified 89 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert90 : signed_kernel_table_aux_Certified 90 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert91 : signed_kernel_table_aux_Certified 91 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert92 : signed_kernel_table_aux_Certified 92 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert93 : signed_kernel_table_aux_Certified 93 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert94 : signed_kernel_table_aux_Certified 94 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert95 : signed_kernel_table_aux_Certified 95 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert96 : signed_kernel_table_aux_Certified 96 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert97 : signed_kernel_table_aux_Certified 97 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert98 : signed_kernel_table_aux_Certified 98 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert99 : signed_kernel_table_aux_Certified 99 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert100 : signed_kernel_table_aux_Certified 100 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert101 : signed_kernel_table_aux_Certified 101 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert102 : signed_kernel_table_aux_Certified 102 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert103 : signed_kernel_table_aux_Certified 103 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert104 : signed_kernel_table_aux_Certified 104 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_cert105 : signed_kernel_table_aux_Certified 105 := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_lowerTable : (351/100 : ℚ) < ∑ q ∈ Finset.Icc 1 105, signed_kernel_table_aux_minorant q := by decide +kernel
set_option maxRecDepth 100000 in
theorem signed_kernel_table_aux_certified {q : ℕ} (hq : q ∈ Finset.Icc 1 105) : signed_kernel_table_aux_Certified q := by
  obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hq
  interval_cases q
  · exact signed_kernel_table_aux_cert1
  · exact signed_kernel_table_aux_cert2
  · exact signed_kernel_table_aux_cert3
  · exact signed_kernel_table_aux_cert4
  · exact signed_kernel_table_aux_cert5
  · exact signed_kernel_table_aux_cert6
  · exact signed_kernel_table_aux_cert7
  · exact signed_kernel_table_aux_cert8
  · exact signed_kernel_table_aux_cert9
  · exact signed_kernel_table_aux_cert10
  · exact signed_kernel_table_aux_cert11
  · exact signed_kernel_table_aux_cert12
  · exact signed_kernel_table_aux_cert13
  · exact signed_kernel_table_aux_cert14
  · exact signed_kernel_table_aux_cert15
  · exact signed_kernel_table_aux_cert16
  · exact signed_kernel_table_aux_cert17
  · exact signed_kernel_table_aux_cert18
  · exact signed_kernel_table_aux_cert19
  · exact signed_kernel_table_aux_cert20
  · exact signed_kernel_table_aux_cert21
  · exact signed_kernel_table_aux_cert22
  · exact signed_kernel_table_aux_cert23
  · exact signed_kernel_table_aux_cert24
  · exact signed_kernel_table_aux_cert25
  · exact signed_kernel_table_aux_cert26
  · exact signed_kernel_table_aux_cert27
  · exact signed_kernel_table_aux_cert28
  · exact signed_kernel_table_aux_cert29
  · exact signed_kernel_table_aux_cert30
  · exact signed_kernel_table_aux_cert31
  · exact signed_kernel_table_aux_cert32
  · exact signed_kernel_table_aux_cert33
  · exact signed_kernel_table_aux_cert34
  · exact signed_kernel_table_aux_cert35
  · exact signed_kernel_table_aux_cert36
  · exact signed_kernel_table_aux_cert37
  · exact signed_kernel_table_aux_cert38
  · exact signed_kernel_table_aux_cert39
  · exact signed_kernel_table_aux_cert40
  · exact signed_kernel_table_aux_cert41
  · exact signed_kernel_table_aux_cert42
  · exact signed_kernel_table_aux_cert43
  · exact signed_kernel_table_aux_cert44
  · exact signed_kernel_table_aux_cert45
  · exact signed_kernel_table_aux_cert46
  · exact signed_kernel_table_aux_cert47
  · exact signed_kernel_table_aux_cert48
  · exact signed_kernel_table_aux_cert49
  · exact signed_kernel_table_aux_cert50
  · exact signed_kernel_table_aux_cert51
  · exact signed_kernel_table_aux_cert52
  · exact signed_kernel_table_aux_cert53
  · exact signed_kernel_table_aux_cert54
  · exact signed_kernel_table_aux_cert55
  · exact signed_kernel_table_aux_cert56
  · exact signed_kernel_table_aux_cert57
  · exact signed_kernel_table_aux_cert58
  · exact signed_kernel_table_aux_cert59
  · exact signed_kernel_table_aux_cert60
  · exact signed_kernel_table_aux_cert61
  · exact signed_kernel_table_aux_cert62
  · exact signed_kernel_table_aux_cert63
  · exact signed_kernel_table_aux_cert64
  · exact signed_kernel_table_aux_cert65
  · exact signed_kernel_table_aux_cert66
  · exact signed_kernel_table_aux_cert67
  · exact signed_kernel_table_aux_cert68
  · exact signed_kernel_table_aux_cert69
  · exact signed_kernel_table_aux_cert70
  · exact signed_kernel_table_aux_cert71
  · exact signed_kernel_table_aux_cert72
  · exact signed_kernel_table_aux_cert73
  · exact signed_kernel_table_aux_cert74
  · exact signed_kernel_table_aux_cert75
  · exact signed_kernel_table_aux_cert76
  · exact signed_kernel_table_aux_cert77
  · exact signed_kernel_table_aux_cert78
  · exact signed_kernel_table_aux_cert79
  · exact signed_kernel_table_aux_cert80
  · exact signed_kernel_table_aux_cert81
  · exact signed_kernel_table_aux_cert82
  · exact signed_kernel_table_aux_cert83
  · exact signed_kernel_table_aux_cert84
  · exact signed_kernel_table_aux_cert85
  · exact signed_kernel_table_aux_cert86
  · exact signed_kernel_table_aux_cert87
  · exact signed_kernel_table_aux_cert88
  · exact signed_kernel_table_aux_cert89
  · exact signed_kernel_table_aux_cert90
  · exact signed_kernel_table_aux_cert91
  · exact signed_kernel_table_aux_cert92
  · exact signed_kernel_table_aux_cert93
  · exact signed_kernel_table_aux_cert94
  · exact signed_kernel_table_aux_cert95
  · exact signed_kernel_table_aux_cert96
  · exact signed_kernel_table_aux_cert97
  · exact signed_kernel_table_aux_cert98
  · exact signed_kernel_table_aux_cert99
  · exact signed_kernel_table_aux_cert100
  · exact signed_kernel_table_aux_cert101
  · exact signed_kernel_table_aux_cert102
  · exact signed_kernel_table_aux_cert103
  · exact signed_kernel_table_aux_cert104
  · exact signed_kernel_table_aux_cert105

set_option maxRecDepth 100000 in
theorem signed_kernel_table
    (n : ℕ) (kernel : ℕ → ℝ) (hn : 30 ∣ n)
    (hkernel : ∀ q ∈ FixedModelBoundsBlueprint.Q,
      0 ≤ kernel q ∧ kernel q ≤ 1)
    (hdivisors : ∀ q ∈ FixedModelBoundsBlueprint.Q, q ∣ 30 →
      1 - 2 * (q : ℝ) / (9 * 105) ≤ kernel q) :
    (351 / 100 : ℝ) <
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        (ArithmeticFunction.moebius q : ℝ) ^ 2 /
            (Nat.totient q : ℝ) ^ 2 *
          FixedModelBoundsBlueprint.R q n * kernel q := by
  classical
  have total : (351/100 : ℝ) <
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        (signed_kernel_table_aux_minorant q : ℝ) := by
    simpa only [FixedModelBoundsBlueprint.Q, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_sum] using
      (Rat.cast_lt (K := ℝ)).mpr signed_kernel_table_aux_lowerTable
  apply total.trans_le
  apply Finset.sum_le_sum
  intro q hq
  have hq' : q ∈ Finset.Icc (1:ℕ) 105 := hq
  let t := q.gcd n
  have qpos : 0 < q := (Finset.mem_Icc.mp hq').1
  have ht : t ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, qpos.ne'⟩
  have hgt : q.gcd 30 ∣ t :=
    Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right q 30).trans hn)
  obtain ⟨hlo, hhi⟩ := signed_kernel_table_aux_certified hq' t ht hgt
  have realLo : (signed_kernel_table_aux_minorant q : ℝ) ≤
      (signed_kernel_table_aux_coef q t : ℝ) *
        (signed_kernel_table_aux_leftEnd q : ℝ) := by exact_mod_cast hlo
  have realHi : (signed_kernel_table_aux_minorant q : ℝ) ≤
      (signed_kernel_table_aux_coef q t : ℝ) := by exact_mod_cast hhi
  have lowK : (signed_kernel_table_aux_leftEnd q : ℝ) ≤ kernel q := by
    by_cases hd : q ∣ 30
    · simpa [signed_kernel_table_aux_leftEnd, hd] using hdivisors q hq hd
    · simpa [signed_kernel_table_aux_leftEnd, hd] using (hkernel q hq).1
  have mid : (signed_kernel_table_aux_minorant q : ℝ) ≤
      (signed_kernel_table_aux_coef q t : ℝ) * kernel q := by
    by_cases hc : 0 ≤ (signed_kernel_table_aux_coef q t : ℝ)
    · exact realLo.trans (mul_le_mul_of_nonneg_left lowK hc)
    · exact realHi.trans (by simpa using
        mul_le_mul_of_nonpos_left (hkernel q hq).2 (le_of_not_ge hc))
  have filterEq : q.divisors.filter (fun d => d ∣ t) =
      q.divisors.filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hdt⟩
      exact ⟨hd, hdt.trans (Nat.gcd_dvd_right q n)⟩
    · rintro ⟨hd, hdn⟩
      exact ⟨hd, Nat.dvd_gcd (Nat.mem_divisors.mp hd).1 hdn⟩
  simpa [signed_kernel_table_aux_coef, signed_kernel_table_aux_ram, filterEq,
    FixedModelBoundsBlueprint.R] using mid

set_option maxRecDepth 100000 in
theorem reciprocal_totient_sum_aux_sqfree (q : ℕ) (h1 : 1 ≤ q) (h2 : q ≤ 105) :
    Squarefree q ↔ ∀ a ∈ Finset.range 11, a * a ∣ q → a = 1 := by
  constructor
  · intro h a ha hdiv
    exact Nat.isUnit_iff.mp (h a hdiv)
  · intro h a hdiv
    have hle : a * a ≤ q := Nat.le_of_dvd h1 hdiv
    have ha11 : a < 11 := by
      by_contra hn
      have h11 : 11 ≤ a := by omega
      have hmul : 11 * 11 ≤ a * a := Nat.mul_le_mul h11 h11
      omega
    exact Nat.isUnit_iff.mpr (h a (Finset.mem_range.mpr ha11) hdiv)

set_option maxRecDepth 100000 in
theorem reciprocal_totient_sum_aux_moebius (q : ℕ) :
    ((ArithmeticFunction.moebius q : ℝ)) ^ 2 = if Squarefree q then (1 : ℝ) else 0 := by
  have h : ((ArithmeticFunction.moebius q : ℝ)) ^ 2
      = ((ArithmeticFunction.moebius q ^ 2 : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, ArithmeticFunction.moebius_sq]
  by_cases hq : Squarefree q
  · simp [hq]
  · simp [hq]

set_option maxRecDepth 100000 in
theorem reciprocal_totient_sum_aux_dvd :
    ∀ q ∈ Finset.Icc (1 : ℕ) 105, Nat.totient q ∣ 20103720436800000 := by
  decide

set_option maxRecDepth 100000 in
theorem reciprocal_totient_sum_aux_table :
    (∑ q ∈ Finset.Icc (1 : ℕ) 105,
      (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then
        20103720436800000 / Nat.totient q else 0)) = 120269128428843000 := by
  decide

set_option maxRecDepth 100000 in
theorem reciprocal_totient_sum_aux_ratio :
    (1000 * 120269128428843000 : ℕ) < 5983 * 20103720436800000 := by
  decide

set_option maxRecDepth 100000 in
theorem reciprocal_totient_sum :
    (∑ q ∈ FixedModelBoundsBlueprint.Q,
      (ArithmeticFunction.moebius q : ℝ) ^ 2 /
        (Nat.totient q : ℝ)) < (5983 / 1000 : ℝ) := by
  have hQ : FixedModelBoundsBlueprint.Q = Finset.Icc (1 : ℕ) 105 := rfl
  rw [hQ]
  have hmem : ∀ q ∈ Finset.Icc (1 : ℕ) 105, 1 ≤ q ∧ q ≤ 105 := by
    intro q hq
    exact Finset.mem_Icc.mp hq
  have hdvd : ∀ q ∈ Finset.Icc (1 : ℕ) 105,
      Nat.totient q ∣ 20103720436800000 := reciprocal_totient_sum_aux_dvd
  have h1 : (∑ q ∈ Finset.Icc (1 : ℕ) 105,
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ))
      = ∑ q ∈ Finset.Icc (1 : ℕ) 105,
        (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
          / (Nat.totient q : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨h1q, h2q⟩ := hmem q hq
    have hif : (if Squarefree q then (1 : ℝ) else 0)
        = (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0) :=
      if_congr (reciprocal_totient_sum_aux_sqfree q h1q h2q) rfl rfl
    rw [reciprocal_totient_sum_aux_moebius q, hif]
  rw [h1]
  have h2 : (20103720436800000 : ℝ) *
      (∑ q ∈ Finset.Icc (1 : ℕ) 105,
        (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
          / (Nat.totient q : ℝ)) = (120269128428843000 : ℝ) := by
    have h3 : ∀ q ∈ Finset.Icc (1 : ℕ) 105,
        (20103720436800000 : ℝ) *
            ((if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
              / (Nat.totient q : ℝ))
          = ((if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then
              20103720436800000 / Nat.totient q else (0 : ℕ) : ℕ) : ℝ) := by
      intro q hq
      by_cases hc : (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1)
      · simp only [if_pos hc, Nat.cast_div_charZero (hdvd q hq)]
        ring
      · simp only [if_neg hc]
        simp
    calc (20103720436800000 : ℝ) *
          (∑ q ∈ Finset.Icc (1 : ℕ) 105,
            (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
              / (Nat.totient q : ℝ))
        = ∑ q ∈ Finset.Icc (1 : ℕ) 105,
            (20103720436800000 : ℝ) *
              ((if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
                / (Nat.totient q : ℝ)) := by rw [Finset.mul_sum]
      _ = ∑ q ∈ Finset.Icc (1 : ℕ) 105,
            ((if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then
              20103720436800000 / Nat.totient q else (0 : ℕ) : ℕ) : ℝ) :=
          Finset.sum_congr rfl h3
      _ = ((∑ q ∈ Finset.Icc (1 : ℕ) 105,
            (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then
              20103720436800000 / Nat.totient q else (0 : ℕ) : ℕ) : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
      _ = (120269128428843000 : ℝ) := by
          rw [reciprocal_totient_sum_aux_table]
          norm_num
  have h4 : (∑ q ∈ Finset.Icc (1 : ℕ) 105,
      (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
        / (Nat.totient q : ℝ)) = (120269128428843000 : ℝ) / 20103720436800000 := by
    rw [eq_div_iff (by norm_num : (20103720436800000 : ℝ) ≠ 0)]
    exact (mul_comm _ _).trans h2
  rw [h4]
  norm_num

set_option maxRecDepth 100000 in
theorem signed_discretization_budget_aux_moebius_abs (m : ℕ) :
    |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := m)
  rcases abs_le.mp h with ⟨h1, h2⟩
  rw [abs_le]
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

set_option maxRecDepth 100000 in
theorem signed_discretization_budget_aux_ramanujan_bound (q n : ℕ) (hq : 1 ≤ q) :
    |FixedModelBoundsBlueprint.R q n| ≤ ((q : ℝ) + 1) * (q : ℝ) := by
  have hqpos : 0 < q := hq
  have hsub : q.divisors.filter (fun d => d ∣ n) ⊆ Finset.range (q + 1) := by
    intro d hd
    have hd' : d ∈ q.divisors := (Finset.mem_filter.mp hd).1
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd').1
    have hdle : d ≤ q := Nat.le_of_dvd hqpos hdq
    simp only [Finset.mem_range]
    omega
  calc |FixedModelBoundsBlueprint.R q n|
      = |∑ d ∈ q.divisors.filter (fun d => d ∣ n),
          (d : ℝ) * (ArithmeticFunction.moebius (q / d) : ℝ)| := rfl
    _ ≤ ∑ d ∈ q.divisors.filter (fun d => d ∣ n),
          |(d : ℝ) * (ArithmeticFunction.moebius (q / d) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ q.divisors.filter (fun d => d ∣ n), (d : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        calc |(d : ℝ) * (ArithmeticFunction.moebius (q / d) : ℝ)|
            = (d : ℝ) * |(ArithmeticFunction.moebius (q / d) : ℝ)| := by
              rw [abs_mul, abs_of_nonneg hd0]
          _ ≤ (d : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left
                (signed_discretization_budget_aux_moebius_abs (q / d)) hd0
          _ = (d : ℝ) := mul_one _
    _ ≤ ∑ d ∈ q.divisors.filter (fun d => d ∣ n), (q : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd' : d ∈ q.divisors := (Finset.mem_filter.mp hd).1
        have hdq : d ∣ q := (Nat.mem_divisors.mp hd').1
        exact_mod_cast Nat.le_of_dvd hqpos hdq
    _ = (((q.divisors.filter (fun d => d ∣ n)).card : ℕ) : ℝ) * (q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((q : ℝ) + 1) * (q : ℝ) := by
        have hc : (q.divisors.filter (fun d => d ∣ n)).card ≤ q + 1 :=
          (Finset.card_le_card hsub).trans_eq (Finset.card_range (q + 1))
        have hc' : (((q.divisors.filter (fun d => d ∣ n)).card : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by
          exact_mod_cast hc
        exact mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg q)

set_option maxRecDepth 100000 in
theorem signed_discretization_budget_aux_coeff_bound (q n : ℕ) (hq : 1 ≤ q) :
    |FixedModelBoundsBlueprint.signedCoeff q n| ≤ 2 * (q : ℝ) ^ 2 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hφ : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    have h : (1 : ℕ) ≤ Nat.totient q := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hμsq : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
    have h := signed_discretization_budget_aux_moebius_abs q
    nlinarith [sq_abs ((ArithmeticFunction.moebius q : ℝ)),
      abs_nonneg ((ArithmeticFunction.moebius q : ℝ))]
  have hcoeff : (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (by nlinarith [hφ])).2
    nlinarith [hμsq, hφ]
  calc |FixedModelBoundsBlueprint.signedCoeff q n|
      = ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) *
          |FixedModelBoundsBlueprint.R q n| := by
        rw [FixedModelBoundsBlueprint.signedCoeff, abs_mul,
          abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ 1 * (((q : ℝ) + 1) * (q : ℝ)) := by
        apply mul_le_mul hcoeff
          (signed_discretization_budget_aux_ramanujan_bound q n hq)
          (abs_nonneg _) (by norm_num)
    _ ≤ 2 * (q : ℝ) ^ 2 := by nlinarith [hq1]

set_option maxRecDepth 100000 in
theorem signed_discretization_budget
    (n : ℕ) (hn : 4000000000000000000 ≤ n) :
    |∑ q ∈ FixedModelBoundsBlueprint.Q,
      FixedModelBoundsBlueprint.signedCoeff q n *
        (FixedModelBoundsBlueprint.S n q -
          FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)))| <
      (1 / 100 : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnlarge : (4000000000000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hterm : ∀ q ∈ FixedModelBoundsBlueprint.Q,
      |FixedModelBoundsBlueprint.signedCoeff q n *
        (FixedModelBoundsBlueprint.S n q -
          FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)))| ≤
        8 * Real.pi * (105 : ℝ) ^ 2 / (n : ℝ) := by
    intro q hq
    have hqmem : q ∈ Finset.Icc (1 : ℕ) 105 := hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqmem).1
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    have hres := (rescaled_kernel_bounds n q hn0 hq1).1
    have hcoef := signed_discretization_budget_aux_coeff_bound q n hq1
    have hid : (q : ℝ) ^ 2 * ((105 : ℝ) / (q : ℝ)) ^ 2 = (105 : ℝ) ^ 2 := by
      rw [div_pow]
      field_simp
    calc |FixedModelBoundsBlueprint.signedCoeff q n *
          (FixedModelBoundsBlueprint.S n q -
            FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)))|
        = |FixedModelBoundsBlueprint.signedCoeff q n| *
          |FixedModelBoundsBlueprint.S n q -
            FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ))| := abs_mul _ _
      _ ≤ (2 * (q : ℝ) ^ 2) *
          (4 * Real.pi * ((105 : ℝ) / (q : ℝ)) ^ 2 / (n : ℝ)) :=
          mul_le_mul hcoef hres (abs_nonneg _) (by positivity)
      _ = 8 * Real.pi * (105 : ℝ) ^ 2 / (n : ℝ) := by
          have h1 : (2 : ℝ) * (q : ℝ) ^ 2 *
              (4 * Real.pi * ((105 : ℝ) / (q : ℝ)) ^ 2 / (n : ℝ)) =
              8 * Real.pi * ((q : ℝ) ^ 2 * ((105 : ℝ) / (q : ℝ)) ^ 2) / (n : ℝ) := by
            ring
          rw [h1, hid]
  have hcard : FixedModelBoundsBlueprint.Q.card = 105 := by
    unfold FixedModelBoundsBlueprint.Q
    decide
  calc |∑ q ∈ FixedModelBoundsBlueprint.Q,
          FixedModelBoundsBlueprint.signedCoeff q n *
            (FixedModelBoundsBlueprint.S n q -
              FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)))|
      ≤ ∑ q ∈ FixedModelBoundsBlueprint.Q,
          |FixedModelBoundsBlueprint.signedCoeff q n *
            (FixedModelBoundsBlueprint.S n q -
              FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ FixedModelBoundsBlueprint.Q, 8 * Real.pi * (105 : ℝ) ^ 2 / (n : ℝ) :=
        Finset.sum_le_sum (fun q hq => hterm q hq)
    _ = 105 * (8 * Real.pi * (105 : ℝ) ^ 2 / (n : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        norm_num
    _ < (1 / 100 : ℝ) := by
        have h1 : (105 : ℝ) * (8 * Real.pi * (105 : ℝ) ^ 2 / (n : ℝ)) =
            (105 * (8 * Real.pi * (105 : ℝ) ^ 2)) / (n : ℝ) := by ring
        rw [h1, div_lt_iff₀ hnpos]
        nlinarith [Real.pi_lt_d2, hnlarge]

set_option maxRecDepth 100000 in
theorem signed_model_lower_bound
    (n : ℕ) (hn : 4000000000000000000 ≤ n) (hdiv : 30 ∣ n) :
    (7 / 2 : ℝ) * (n : ℝ) < FixedModelBoundsBlueprint.C n := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hkernel : ∀ q ∈ FixedModelBoundsBlueprint.Q,
      0 ≤ FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)) ∧
        FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)) ≤ 1 := by
    intro q hq
    have hq' : q ∈ Finset.Icc (1 : ℕ) 105 := hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq').1
    have hq0 : 0 < q := by omega
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
    have h105 : (0 : ℝ) < (105 : ℝ) / (q : ℝ) := div_pos (by norm_num) hqR
    exact ⟨(sinc_mass_bounds _ h105).1, (sinc_mass_bounds _ h105).2.1⟩
  have hdivisors : ∀ q ∈ FixedModelBoundsBlueprint.Q, q ∣ 30 →
      1 - 2 * (q : ℝ) / (9 * 105) ≤
        FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)) := by
    intro q hq _
    have hq' : q ∈ Finset.Icc (1 : ℕ) 105 := hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq').1
    have hq0 : 0 < q := by omega
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
    have h105 : (0 : ℝ) < (105 : ℝ) / (q : ℝ) := div_pos (by norm_num) hqR
    have h := (sinc_mass_bounds _ h105).2.2
    have heq : 2 / (9 * ((105 : ℝ) / (q : ℝ))) = 2 * (q : ℝ) / (9 * 105) := by
      field_simp
    rw [heq] at h
    exact h
  have hK : ∀ q ∈ FixedModelBoundsBlueprint.Q,
      FixedModelBoundsBlueprint.signedCoeff q n *
          FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)) =
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
          FixedModelBoundsBlueprint.R q n *
          FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)) := by
    intro q _
    simp only [FixedModelBoundsBlueprint.signedCoeff, mul_assoc]
  have hsplit : (∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.signedCoeff q n * FixedModelBoundsBlueprint.S n q) =
      (∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.signedCoeff q n *
          FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ))) +
      (∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.signedCoeff q n *
          (FixedModelBoundsBlueprint.S n q -
            FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have htable := signed_kernel_table n
    (fun q : ℕ => FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)))
    hdiv hkernel hdivisors
  have htable' : (351 / 100 : ℝ) <
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.signedCoeff q n *
          FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)) := by
    rw [Finset.sum_congr rfl (fun q hq => hK q hq)]
    exact htable
  have hbudget := signed_discretization_budget n hn
  have hmain : (7 / 2 : ℝ) < FixedModelBoundsBlueprint.C n / (n : ℝ) := by
    rw [signed_model_normal_form n, hsplit]
    have h1 := (abs_lt.mp hbudget).1
    linarith [htable']
  exact (lt_div_iff₀ hnR).mp hmain

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_energy_model_normal_form_aux_card (q : ℕ) :
    ((FixedModelBoundsBlueprint.A q).card : ℝ) = (Nat.totient q : ℝ) := by
  have h : (FixedModelBoundsBlueprint.A q).card = Nat.totient q := by
    rw [FixedModelBoundsBlueprint.A, Nat.totient_eq_card_coprime]
    congr 1
    exact Finset.filter_congr fun a _ => Nat.coprime_comm
  exact_mod_cast h

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_energy_model_normal_form_aux_norm (n q : ℕ) (β : ℝ) :
    ‖FixedModelBoundsBlueprint.M n q β‖ ^ 2 =
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
        ‖FixedModelBoundsBlueprint.V n β‖ ^ 2 := by
  simp only [FixedModelBoundsBlueprint.M, Complex.norm_mul, Complex.norm_div,
    Complex.norm_intCast, Complex.norm_natCast, mul_pow, div_pow, sq_abs]

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_energy_model_normal_form_aux_integral (n q : ℕ) :
    FixedModelBoundsBlueprint.Jr (FixedModelBoundsBlueprint.H n q)
        (fun β => ‖FixedModelBoundsBlueprint.M n q β‖ ^ 2) =
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
        FixedModelBoundsBlueprint.Jr (FixedModelBoundsBlueprint.H n q)
          (fun β => ‖FixedModelBoundsBlueprint.V n β‖ ^ 2) := by
  have hfun :
      (fun β => ‖FixedModelBoundsBlueprint.M n q β‖ ^ 2) =
        fun β => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
          ‖FixedModelBoundsBlueprint.V n β‖ ^ 2 :=
    funext fun β => energy_model_upper_bound_aux_energy_model_normal_form_aux_norm n q β
  simp only [FixedModelBoundsBlueprint.Jr, hfun, intervalIntegral.integral_const_mul]

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_energy_model_normal_form (n : ℕ) :
    FixedModelBoundsBlueprint.B n / (n : ℝ) =
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.energyCoeff q *
          FixedModelBoundsBlueprint.T n q := by
  have hφ : ∀ q ∈ FixedModelBoundsBlueprint.Q, (Nat.totient q : ℝ) ≠ 0 := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hpos : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
    exact_mod_cast hpos.ne'
  have hB : FixedModelBoundsBlueprint.B n =
      ∑ q ∈ FixedModelBoundsBlueprint.Q,
        FixedModelBoundsBlueprint.energyCoeff q *
          FixedModelBoundsBlueprint.Jr (FixedModelBoundsBlueprint.H n q)
            (fun β => ‖FixedModelBoundsBlueprint.V n β‖ ^ 2) := by
    simp only [FixedModelBoundsBlueprint.B]
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq0 : (Nat.totient q : ℝ) ≠ 0 := hφ q hq
    rw [energy_model_upper_bound_aux_energy_model_normal_form_aux_card q, energy_model_upper_bound_aux_energy_model_normal_form_aux_integral]
    simp only [FixedModelBoundsBlueprint.energyCoeff]
    field_simp
  rw [hB, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro q _
  simp only [FixedModelBoundsBlueprint.T]
  ring

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_reciprocal_totient_sum_aux_sqfree (q : ℕ) (h1 : 1 ≤ q) (h2 : q ≤ 105) :
    Squarefree q ↔ ∀ a ∈ Finset.range 11, a * a ∣ q → a = 1 := by
  constructor
  · intro h a ha hdiv
    exact Nat.isUnit_iff.mp (h a hdiv)
  · intro h a hdiv
    have hle : a * a ≤ q := Nat.le_of_dvd h1 hdiv
    have ha11 : a < 11 := by
      by_contra hn
      have h11 : 11 ≤ a := by omega
      have hmul : 11 * 11 ≤ a * a := Nat.mul_le_mul h11 h11
      omega
    exact Nat.isUnit_iff.mpr (h a (Finset.mem_range.mpr ha11) hdiv)

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_reciprocal_totient_sum_aux_moebius (q : ℕ) :
    ((ArithmeticFunction.moebius q : ℝ)) ^ 2 = if Squarefree q then (1 : ℝ) else 0 := by
  have h : ((ArithmeticFunction.moebius q : ℝ)) ^ 2
      = ((ArithmeticFunction.moebius q ^ 2 : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, ArithmeticFunction.moebius_sq]
  by_cases hq : Squarefree q
  · simp [hq]
  · simp [hq]

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_reciprocal_totient_sum_aux_dvd :
    ∀ q ∈ Finset.Icc (1 : ℕ) 105, Nat.totient q ∣ 20103720436800000 := by
  decide

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_reciprocal_totient_sum_aux_table :
    (∑ q ∈ Finset.Icc (1 : ℕ) 105,
      (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then
        20103720436800000 / Nat.totient q else 0)) = 120269128428843000 := by
  decide

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_reciprocal_totient_sum_aux_ratio :
    (1000 * 120269128428843000 : ℕ) < 5983 * 20103720436800000 := by
  decide

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_reciprocal_totient_sum :
    (∑ q ∈ FixedModelBoundsBlueprint.Q,
      (ArithmeticFunction.moebius q : ℝ) ^ 2 /
        (Nat.totient q : ℝ)) < (5983 / 1000 : ℝ) := by
  have hQ : FixedModelBoundsBlueprint.Q = Finset.Icc (1 : ℕ) 105 := rfl
  rw [hQ]
  have hmem : ∀ q ∈ Finset.Icc (1 : ℕ) 105, 1 ≤ q ∧ q ≤ 105 := by
    intro q hq
    exact Finset.mem_Icc.mp hq
  have hdvd : ∀ q ∈ Finset.Icc (1 : ℕ) 105,
      Nat.totient q ∣ 20103720436800000 := energy_model_upper_bound_aux_reciprocal_totient_sum_aux_dvd
  have h1 : (∑ q ∈ Finset.Icc (1 : ℕ) 105,
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ))
      = ∑ q ∈ Finset.Icc (1 : ℕ) 105,
        (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
          / (Nat.totient q : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨h1q, h2q⟩ := hmem q hq
    have hif : (if Squarefree q then (1 : ℝ) else 0)
        = (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0) :=
      if_congr (energy_model_upper_bound_aux_reciprocal_totient_sum_aux_sqfree q h1q h2q) rfl rfl
    rw [energy_model_upper_bound_aux_reciprocal_totient_sum_aux_moebius q, hif]
  rw [h1]
  have h2 : (20103720436800000 : ℝ) *
      (∑ q ∈ Finset.Icc (1 : ℕ) 105,
        (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
          / (Nat.totient q : ℝ)) = (120269128428843000 : ℝ) := by
    have h3 : ∀ q ∈ Finset.Icc (1 : ℕ) 105,
        (20103720436800000 : ℝ) *
            ((if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
              / (Nat.totient q : ℝ))
          = ((if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then
              20103720436800000 / Nat.totient q else (0 : ℕ) : ℕ) : ℝ) := by
      intro q hq
      by_cases hc : (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1)
      · simp only [if_pos hc, Nat.cast_div_charZero (hdvd q hq)]
        ring
      · simp only [if_neg hc]
        simp
    calc (20103720436800000 : ℝ) *
          (∑ q ∈ Finset.Icc (1 : ℕ) 105,
            (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
              / (Nat.totient q : ℝ))
        = ∑ q ∈ Finset.Icc (1 : ℕ) 105,
            (20103720436800000 : ℝ) *
              ((if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
                / (Nat.totient q : ℝ)) := by rw [Finset.mul_sum]
      _ = ∑ q ∈ Finset.Icc (1 : ℕ) 105,
            ((if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then
              20103720436800000 / Nat.totient q else (0 : ℕ) : ℕ) : ℝ) :=
          Finset.sum_congr rfl h3
      _ = ((∑ q ∈ Finset.Icc (1 : ℕ) 105,
            (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then
              20103720436800000 / Nat.totient q else (0 : ℕ) : ℕ) : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
      _ = (120269128428843000 : ℝ) := by
          rw [energy_model_upper_bound_aux_reciprocal_totient_sum_aux_table]
          norm_num
  have h4 : (∑ q ∈ Finset.Icc (1 : ℕ) 105,
      (if (∀ a ∈ Finset.range 11, a * a ∣ q → a = 1) then (1 : ℝ) else 0)
        / (Nat.totient q : ℝ)) = (120269128428843000 : ℝ) / 20103720436800000 := by
    rw [eq_div_iff (by norm_num : (20103720436800000 : ℝ) ≠ 0)]
    exact (mul_comm _ _).trans h2
  rw [h4]
  norm_num

section

open MeasureTheory Real Complex Set Filter
open scoped FourierTransform Convolution Topology RealInnerProductSpace

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
def energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff {t : ℝ} : t ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset ↔ -(1 / 2 : ℝ) ≤ t ∧ t ≤ 1 / 2 := Iff.rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_meas : MeasurableSet energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset := measurableSet_Icc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_neg_mem {t : ℝ} : -t ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset ↔ t ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset := by
  rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff, energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff]
  constructor
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
def energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind : ℝ → ℂ := energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset.indicator (fun _ => 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_mem {t : ℝ} (ht : t ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset) : energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t = 1 := by
  simp only [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind, Set.indicator_of_mem ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem {t : ℝ} (ht : t ∉ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset) : energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t = 0 := by
  simp only [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind, Set.indicator_of_notMem ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_even (t : ℝ) : energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (-t) = energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t := by
  by_cases ht : t ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset
  · rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_mem (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_neg_mem.mpr ht), energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_mem ht]
  · rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem (fun h => ht (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_neg_mem.mp h)), energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_mul_self (t : ℝ) : energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t * energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t = energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t := by
  by_cases ht : t ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset
  · rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_mem ht, one_mul]
  · rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem ht, mul_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_measure_ne_top : volume energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset ≠ ⊤ := by
  have h : volume energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset < ⊤ := isCompact_Icc.measure_lt_top
  exact h.ne

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_integrable : Integrable energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind := by
  rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind, integrable_indicator_iff energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_meas]
  exact integrableOn_const energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_measure_ne_top

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_integral_hind : ∫ t : ℝ, energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t = 1 := by
  have h1 : (∫ t : ℝ, energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t) = volume.real energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset • (1 : ℂ) := by
    rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind, integral_indicator_const (1 : ℂ) energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_meas]
  rw [h1]
  have h2 : volume.real energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset = 1 := by
    show volume.real (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) = 1
    rw [Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
  rw [h2]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_ft (w : ℝ) : 𝓕 energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind w = ((Real.sinc (Real.pi * w) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  simp only [Real.inner_apply]
  have hpt : ∀ v : ℝ, Complex.exp ((↑(-2 * Real.pi * (v * w)) : ℂ) * Complex.I) • energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind v
      = energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset.indicator
          (fun v : ℝ => Complex.exp ((↑(-2 * Real.pi * (v * w)) : ℂ) * Complex.I)) v := by
    intro v
    by_cases hv : v ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset
    · rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_mem hv, Set.indicator_of_mem hv, smul_eq_mul, mul_one]
    · rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem hv, Set.indicator_of_notMem hv, smul_zero]
  simp_rw [hpt]
  rw [MeasureTheory.integral_indicator energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_meas]
  simp only [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hrw : ∀ x : ℝ, (-2 * Real.pi * (x * w)) = ((-2 * Real.pi * w) * x) := by
    intro x
    ring
  have hrw' : ∀ x : ℝ, (↑(-2 * Real.pi * (x * w)) : ℂ) = ↑((-2 * Real.pi * w) * x) := by
    intro x
    rw [hrw x]
  simp_rw [hrw']
  by_cases hw : w = 0
  · subst hw
    have hc0 : (fun x : ℝ => Complex.exp ((↑((-2 * Real.pi * 0) * x) : ℂ) * Complex.I))
        = fun _ => (1 : ℂ) := by
      funext x
      simp
    rw [hc0, intervalIntegral.integral_const]
    simp [Real.sinc_zero]
    norm_num
  · have hne : (-2 * Real.pi * w) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) Real.pi_ne_zero) hw
    have hstep : (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          Complex.exp ((↑((-2 * Real.pi * w) * x) : ℂ) * Complex.I))
        = (-2 * Real.pi * w)⁻¹ • ∫ t in ((-2 * Real.pi * w) * (-(1 / 2 : ℝ)))..((-2 * Real.pi * w) * (1 / 2)),
            Complex.exp ((↑t : ℂ) * Complex.I) :=
      intervalIntegral.integral_comp_mul_left
        (fun t : ℝ => Complex.exp ((↑t : ℂ) * Complex.I)) hne
    rw [hstep]
    have e1 : (-2 * Real.pi * w) * (-(1 / 2 : ℝ)) = Real.pi * w := by ring
    have e2 : (-2 * Real.pi * w) * (1 / 2 : ℝ) = -(Real.pi * w) := by ring
    rw [e1, e2, intervalIntegral.integral_symm, integral_exp_mul_I_eq_sinc]
    rw [Complex.real_smul]
    have hkey : ((-2 * Real.pi * w)⁻¹ * -(2 * (Real.pi * w) * Real.sinc (Real.pi * w)) : ℝ)
        = Real.sinc (Real.pi * w) := by
      field_simp [hne] <;> ring
    calc _ = ((↑((-2 * Real.pi * w)⁻¹
            * -(2 * (Real.pi * w) * Real.sinc (Real.pi * w))) : ℂ)) := by
          push_cast <;> ring
      _ = _ := by rw [hkey]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_eventuallyEq (s : ℝ) (h1 : s ≠ -(1 / 2 : ℝ)) (h2 : s ≠ (1 / 2 : ℝ)) :
    ∀ᶠ y in 𝓝 s, energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind y = energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind s := by
  by_cases hs1 : (-(1 / 2 : ℝ)) < s
  · by_cases hs2 : s < (1 / 2 : ℝ)
    · have hm : s ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset := energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff.mpr ⟨le_of_lt hs1, le_of_lt hs2⟩
      filter_upwards [Ioo_mem_nhds hs1 hs2] with y hy
      have hy' := Set.mem_Ioo.mp hy
      rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_mem (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff.mpr ⟨le_of_lt hy'.1, le_of_lt hy'.2⟩), energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_mem hm]
    · have hs2' : (1 / 2 : ℝ) < s := lt_of_le_of_ne (le_of_not_gt hs2) (fun hcon => h2 hcon.symm)
      have hm : s ∉ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset :=
        fun hx => absurd (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff.mp hx).2 (by linarith : ¬ (s ≤ 1 / 2))
      filter_upwards [Ioi_mem_nhds hs2'] with y hy
      have hy' := Set.mem_Ioi.mp hy
      rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem
          (fun hx => absurd (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff.mp hx).2 (by linarith : ¬ (y ≤ 1 / 2))),
        energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem hm]
  · have hs1' : s < -(1 / 2 : ℝ) := lt_of_le_of_ne (le_of_not_gt hs1) h1
    have hm : s ∉ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset :=
      fun hx => absurd (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff.mp hx).1 (by linarith : ¬ (-(1 / 2 : ℝ) ≤ s))
    filter_upwards [Iio_mem_nhds hs1'] with y hy
    have hy' := Set.mem_Iio.mp hy
    rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem
        (fun hx => absurd (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset_mem_iff.mp hx).1 (by linarith : ¬ (-(1 / 2 : ℝ) ≤ y))),
      energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem hm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_convolution_hind_continuousAt_zero :
    ContinuousAt (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind) 0 := by
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun t => energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t * energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (x - t)) volume := by
    intro x
    simpa using (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_integrable.aestronglyMeasurable.convolution_integrand_snd
      (ContinuousLinearMap.mul ℂ ℂ) energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_integrable.aestronglyMeasurable x)
  have hbound : ∀ x t : ℝ, ‖energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t * energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (x - t)‖ ≤ ‖energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t‖ := by
    intro x t
    have h3 : ‖energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (x - t)‖ ≤ 1 := by
      by_cases hmem : (x - t) ∈ energy_model_upper_bound_aux_sinc_mass_bounds_aux_hset
      · rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_mem hmem]
        simp
      · rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_of_notMem hmem]
        simp
    rw [norm_mul]
    calc ‖energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t‖ * ‖energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (x - t)‖ ≤ ‖energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t‖ * 1 :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ‖energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t‖ := mul_one _
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun x => energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t * energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (x - t)) (𝓝 (0 : ℝ))
      (𝓝 (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t * energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (-t))) := by
    filter_upwards [MeasureTheory.volume.ae_ne (-(1 / 2 : ℝ)),
      MeasureTheory.volume.ae_ne (1 / 2 : ℝ)] with t h1 h2
    have hsub : Tendsto (fun x : ℝ => x - t) (𝓝 (0 : ℝ)) (𝓝 (-t)) := by
      have hc : ContinuousAt (fun x : ℝ => x - t) 0 := by fun_prop
      simpa using hc.tendsto
    have hkey : ∀ᶠ y in 𝓝 (-t), energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind y = energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (-t) :=
      energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_eventuallyEq (-t) (fun hcon => h2 (by linarith)) (fun hcon => h1 (by linarith))
    have hconv : Tendsto (fun x : ℝ => energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (x - t)) (𝓝 (0 : ℝ)) (𝓝 (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (-t))) := by
      refine (tendsto_const_nhds.congr' ?_)
      filter_upwards [hsub.eventually hkey] with x hx
      exact hx.symm
    exact tendsto_const_nhds.mul hconv
  have hmain : Tendsto (fun x : ℝ => ∫ t, energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t * energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (x - t)) (𝓝 (0 : ℝ))
      (𝓝 (∫ t, energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t * energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (-t))) :=
    tendsto_integral_filter_of_dominated_convergence (fun t => ‖energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t‖)
      (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall (hbound x))
      energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_integrable.norm hlim
  have hout : Tendsto (fun x : ℝ => (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind) x) (𝓝 (0 : ℝ))
      (𝓝 ((energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind) 0)) := by
    simpa only [convolution_mul, zero_sub] using hmain
  exact hout

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_nonneg (t : ℝ) : 0 ≤ Real.sinc (Real.pi * t) ^ 2 := sq_nonneg _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le_one (t : ℝ) : Real.sinc (Real.pi * t) ^ 2 ≤ 1 := by
  have hA := Real.sinc_le_one (Real.pi * t)
  have hB := Real.neg_one_le_sinc (Real.pi * t)
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_even (t : ℝ) :
    Real.sinc (Real.pi * (-t)) ^ 2 = Real.sinc (Real.pi * t) ^ 2 := by
  rw [mul_neg, Real.sinc_neg]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le (t : ℝ) (ht : t ≠ 0) :
    Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := by
  have hpi : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
  rw [Real.sinc_of_ne_zero hpi]
  have h1 : Real.sin (Real.pi * t) ^ 2 ≤ 1 := by
    have hA := Real.sin_le_one (Real.pi * t)
    have hB := Real.neg_one_le_sin (Real.pi * t)
    nlinarith
  have h2 : (0 : ℝ) < Real.pi ^ 2 * t ^ 2 := by positivity
  have h3 : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
  calc (Real.sin (Real.pi * t) / (Real.pi * t)) ^ 2
      = Real.sin (Real.pi * t) ^ 2 / (Real.pi ^ 2 * t ^ 2) := by rw [div_pow, h3]
    _ ≤ 1 / (Real.pi ^ 2 * t ^ 2) := div_le_div_of_nonneg_right h1 h2.le

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le_inv (t : ℝ) (ht : t ≠ 0) :
    Real.sinc (Real.pi * t) ^ 2 ≤ (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ := by
  calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le t ht
    _ = (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ := by rw [div_eq_mul_inv, one_mul, mul_inv_rev]; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le_two (t : ℝ) :
    Real.sinc (Real.pi * t) ^ 2 ≤ 2 / (1 + (Real.pi * t) ^ 2) := by
  have hrw : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
  have hden : (0 : ℝ) < 1 + Real.pi ^ 2 * t ^ 2 := by positivity
  by_cases ht : t = 0
  · subst ht
    norm_num [Real.sinc_zero]
  · have hu0 : (0 : ℝ) < Real.pi ^ 2 * t ^ 2 := by positivity
    rcases le_or_gt (Real.pi ^ 2 * t ^ 2) 1 with h | h
    · have h2 : (1 : ℝ) ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := by
        rw [le_div_iff₀ hden]
        linarith
      calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 := energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le_one t
        _ ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := h2
        _ = 2 / (1 + (Real.pi * t) ^ 2) := by rw [hrw]
    · have h3 : 1 / (Real.pi ^ 2 * t ^ 2) ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := by
        rw [div_le_div_iff₀ hu0 hden]
        nlinarith
      calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le t ht
        _ ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := h3
        _ = 2 / (1 + (Real.pi * t) ^ 2) := by rw [hrw]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_integrable : Integrable (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) := by
    fun_prop
  have hG : Integrable (fun t : ℝ => 2 / (1 + (Real.pi * t) ^ 2)) := by
    have h2 : Integrable (fun x : ℝ => 2 * (1 + x ^ 2) ⁻¹) :=
      integrable_inv_one_add_sq.const_mul 2
    have h3 : Integrable (fun t : ℝ => 2 * (1 + (Real.pi * t) ^ 2) ⁻¹) :=
      h2.comp_mul_left' Real.pi_ne_zero
    refine h3.congr (ae_of_all _ fun t => ?_)
    simp only [div_eq_mul_inv]
  refine Integrable.mono' hG hcont.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_nonneg t)]
  exact energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le_two t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_total : ∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 = 1 := by
  have hT_int : Integrable (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind) :=
    energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_integrable
  have hFT : ∀ ξ : ℝ, 𝓕 (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind) ξ
      = ((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ) := by
    intro ξ
    rw [Real.fourier_mul_convolution_eq energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_integrable energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_integrable ξ, energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_ft ξ]
    push_cast
    ring
  have hFT_int : Integrable (𝓕 (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind)) := by
    have h1 : Integrable (fun ξ : ℝ => ((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ)) :=
      Integrable.iff_ofReal.mp energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_integrable
    exact h1.congr (ae_of_all _ fun ξ => (hFT ξ).symm)
  have hinv : 𝓕⁻ (𝓕 (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind)) 0
      = (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind) 0 :=
    hT_int.fourierInv_fourier_eq hFT_int energy_model_upper_bound_aux_sinc_mass_bounds_aux_convolution_hind_continuousAt_zero
  have hT0 : (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind) 0 = 1 := by
    rw [convolution_mul]
    simp only [zero_sub]
    have hself : ∀ t : ℝ, energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t * energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind (-t) = energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind t := by
      intro t
      rw [energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_even t]
      exact energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind_mul_self t
    simp_rw [hself]
    exact energy_model_upper_bound_aux_sinc_mass_bounds_aux_integral_hind
  have hF0 : 𝓕⁻ (𝓕 (energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind ⋆[ContinuousLinearMap.mul ℂ ℂ] energy_model_upper_bound_aux_sinc_mass_bounds_aux_hind)) 0
      = ((∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ) := by
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    rw [integral_congr_ae (ae_of_all _ fun v => hFT v)]
    first
      | exact integral_ofReal
      | norm_cast
  have hfin : ((∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hF0, hinv, hT0]
  exact Complex.ofReal_inj.mp hfin

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma energy_model_upper_bound_aux_sinc_mass_bounds_aux_trunc_bound (f : ℝ → ℝ) (hf_nonneg : ∀ t, 0 ≤ f t) (hf_even : ∀ t, f (-t) = f t)
    (hf_bound : ∀ t, t ≠ 0 → f t ≤ (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹)
    (hf_int : Integrable f) (hf_tot : ∫ t : ℝ, f t = 1) (h : ℝ) (hh : 0 < h) :
    let k := intervalIntegral (fun t : ℝ => f t) (-h) h MeasureTheory.volume
    0 ≤ k ∧ k ≤ 1 ∧ 1 - 2 / (9 * h) ≤ k := by
  dsimp only
  have hle : -h ≤ h := by linarith
  have hk : intervalIntegral (fun t : ℝ => f t) (-h) h volume
      = ∫ t in Ioc (-h) h, f t ∂volume := intervalIntegral.integral_of_le hle
  have hbound_int : IntegrableOn (fun t : ℝ => (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹) (Ioi h) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi h) :=
      integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := h) (by norm_num) hh
    have hmul : IntegrableOn (fun t : ℝ => (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ)) (Ioi h) :=
      hbase.const_mul _
    refine hmul.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have htpos : 0 < t := hh.trans ht
    show (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ) = (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg htpos.le, Real.rpow_two]
  have htail : ∫ t in Ioi h, f t ∂volume ≤ (Real.pi ^ 2)⁻¹ * h⁻¹ := by
    have hA : ∫ t in Ioi h, f t ∂volume ≤ ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume :=
      setIntegral_mono_on hf_int.integrableOn hbound_int measurableSet_Ioi
        (fun t ht => hf_bound t (ne_of_gt (lt_of_lt_of_le hh ht.le)))
    have hB : ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume = (Real.pi ^ 2)⁻¹ * h⁻¹ := by
      have hc : ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume
          = ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ) ∂volume := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        have htpos : 0 < t := hh.trans ht
        show (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ = (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ)
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg htpos.le, Real.rpow_two]
      rw [hc, integral_const_mul, integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hh]
      have h3 : (-h ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1)) = h⁻¹ := by
        rw [show (-2 : ℝ) + 1 = -1 by ring, Real.rpow_neg_one]
        simp
      rw [h3]
    linarith [hA, hB]
  have hleft : ∫ t in Iic (-h), f t ∂volume = ∫ t in Ioi h, f t ∂volume := by
    have h1 : ∫ t in Iic (-h), f t ∂volume = ∫ t in Iic (-h), f (-t) ∂volume :=
      setIntegral_congr_fun measurableSet_Iic (fun x _ => (hf_even x).symm)
    rw [h1, integral_comp_neg_Iic (-h) f]
    simp
  have hpi : (9 : ℝ) < Real.pi ^ 2 := by
    have h4 := Real.pi_gt_three
    nlinarith
  have hinv : (Real.pi ^ 2)⁻¹ ≤ (9 : ℝ)⁻¹ := by
    have h5 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) hpi.le
    simpa using h5
  have htail' : ∫ t in Ioi h, f t ∂volume ≤ (9 : ℝ)⁻¹ * h⁻¹ := by
    have h6 := mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr hh.le)
    linarith [htail, h6]
  have hcomp : ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume
      = ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume := by
    rw [compl_Ioc]
    exact setIntegral_union (Iic_disjoint_Ioi hle) measurableSet_Ioi hf_int.integrableOn
      hf_int.integrableOn
  have htotal : (∫ t in Ioc (-h) h, f t ∂volume) + ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume = 1 := by
    rw [integral_add_compl measurableSet_Ioc hf_int]
    exact hf_tot
  have hnn : 0 ≤ ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume :=
    setIntegral_nonneg measurableSet_Ioc.compl (fun u _ => hf_nonneg u)
  have htail2 : ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume ≤ 2 / (9 * h) := by
    have hA : ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume ≤ 2 * ((9 : ℝ)⁻¹ * h⁻¹) := by
      rw [hleft]
      linarith [htail']
    have hB : 2 * ((9 : ℝ)⁻¹ * h⁻¹) = 2 / (9 * h) := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ring
    linarith [hA, hB]
  refine ⟨?_, ?_, ?_⟩
  · exact intervalIntegral.integral_nonneg hle (fun u _ => hf_nonneg u)
  · rw [hk]
    linarith [htotal, hnn]
  · rw [hk]
    rw [hcomp] at htotal
    linarith [htotal, htail2]

end

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_sinc_mass_bounds (h : ℝ) (hh : 0 < h) :
    0 ≤ FixedModelBoundsBlueprint.K h ∧
      FixedModelBoundsBlueprint.K h ≤ 1 ∧
      1 - 2 / (9 * h) ≤ FixedModelBoundsBlueprint.K h := by
  have hmain := energy_model_upper_bound_aux_sinc_mass_bounds_aux_trunc_bound
    (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2)
    energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_nonneg
    energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_even
    energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_le_inv
    energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_integrable
    energy_model_upper_bound_aux_sinc_mass_bounds_aux_sinc_sq_total h hh
  simpa [FixedModelBoundsBlueprint.K, FixedModelBoundsBlueprint.Jr] using hmain

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
noncomputable def energy_model_upper_bound_aux_phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
noncomputable def energy_model_upper_bound_aux_polysum (n : ℕ) (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 n, energy_model_upper_bound_aux_phase (k*x)
open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
noncomputable def energy_model_upper_bound_aux_target (t : ℝ) := energy_model_upper_bound_aux_phase (t/2)*(Real.sinc (Real.pi*t):ℂ)

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_phaseNorm (x : ℝ) : ‖energy_model_upper_bound_aux_phase x‖=1 := Complex.norm_exp_ofReal_mul_I _
open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_phaseAdd (x y : ℝ) : energy_model_upper_bound_aux_phase (x+y)=energy_model_upper_bound_aux_phase x*energy_model_upper_bound_aux_phase y := by
  simp only [energy_model_upper_bound_aux_phase, mul_add, Complex.ofReal_add,add_mul,Complex.exp_add]
open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_phaseLip (x y : ℝ) : ‖energy_model_upper_bound_aux_phase x-energy_model_upper_bound_aux_phase y‖ ≤ 2*Real.pi*|x-y| := by
  have h : energy_model_upper_bound_aux_phase x-energy_model_upper_bound_aux_phase y = (energy_model_upper_bound_aux_phase (x-y)-1)*energy_model_upper_bound_aux_phase y := by
    rw [sub_mul, ← energy_model_upper_bound_aux_phaseAdd, sub_add_cancel,one_mul]
  rw [h,norm_mul,energy_model_upper_bound_aux_phaseNorm,mul_one]
  unfold energy_model_upper_bound_aux_phase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul]
  rw [show 2*Real.pi*(x-y)/2=Real.pi*(x-y) by ring]
  have hb : |Real.sin (Real.pi*(x-y))| ≤ |Real.pi*(x-y)| := Real.abs_sin_le_abs
  rw [abs_mul,abs_of_pos Real.pi_pos] at hb
  norm_num
  linarith

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_continuousPhase : Continuous energy_model_upper_bound_aux_phase := by unfold energy_model_upper_bound_aux_phase; fun_prop
open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_continuousPoly (n : ℕ) : Continuous (energy_model_upper_bound_aux_polysum n) := by unfold energy_model_upper_bound_aux_polysum energy_model_upper_bound_aux_phase; fun_prop
open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_continuousTarget : Continuous energy_model_upper_bound_aux_target := by unfold energy_model_upper_bound_aux_target energy_model_upper_bound_aux_phase; fun_prop
open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_targetNorm (t : ℝ) : ‖energy_model_upper_bound_aux_target t‖ ≤ 1 := by
  simpa [energy_model_upper_bound_aux_target,norm_mul,energy_model_upper_bound_aux_phaseNorm,Complex.norm_real,Real.norm_eq_abs] using Real.abs_sinc_le_one (Real.pi*t)

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_kernelInt (t : ℝ) : (∫ x in (0:ℝ)..1, energy_model_upper_bound_aux_phase (x*t)) = energy_model_upper_bound_aux_target t := by
  by_cases ht : t=0
  · subst t; simp [energy_model_upper_bound_aux_phase,energy_model_upper_bound_aux_target]
  let a := Real.pi*t
  have ha : a ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
  let w := fun z : ℝ => Complex.exp ((z:ℂ)*Complex.I)
  have fac (x : ℝ) : energy_model_upper_bound_aux_phase (x*t) = energy_model_upper_bound_aux_phase (t/2)*w ((2*a)*x-a) := by
    simp only [energy_model_upper_bound_aux_phase,w,← Complex.exp_add]
    congr 1
    dsimp [a]; push_cast; ring
  simp_rw [fac]
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_mul_add (a:=(0:ℝ)) (b:=1) w
    (show 2*a ≠ 0 by positivity) (-a)
  simp only [mul_zero,zero_add,mul_one,show 2*a + -a = a by ring] at h
  change _ * (∫ x in (0:ℝ)..1, w (2*a*x + -a)) = _
  rw [h]
  change energy_model_upper_bound_aux_phase (t/2)* ((2*a)⁻¹ • (∫ z in -a..a, Complex.exp ((z:ℂ)*Complex.I))) = _
  rw [integral_exp_mul_I_eq_sinc,Complex.real_smul]
  change energy_model_upper_bound_aux_phase (t/2) * _ = energy_model_upper_bound_aux_phase (t/2) * (Real.sinc a : ℂ)
  congr 1
  push_cast
  field_simp [show (a:ℂ)≠0 by exact_mod_cast ha]

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_rangePoly (n : ℕ) (y : ℝ) :
    energy_model_upper_bound_aux_polysum n y = ∑ k ∈ Finset.range n, energy_model_upper_bound_aux_phase (((k:ℝ)+1)*y) := by
  unfold energy_model_upper_bound_aux_polysum
  rw [← Finset.Ico_succ_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_cell (u : ℝ) (j : ℕ) :
    ‖energy_model_upper_bound_aux_phase (((j:ℝ)+1)*u) - ∫ x in (j:ℝ)..((j:ℝ)+1), energy_model_upper_bound_aux_phase (x*u)‖ ≤ Real.pi*|u| := by
  let b : ℝ := j+1
  let a : ℝ := j
  let g := fun x : ℝ => energy_model_upper_bound_aux_phase (x*u)
  have hab : a≤b := by dsimp [a,b]; linarith
  have hg : Continuous g := energy_model_upper_bound_aux_continuousPhase.comp (continuous_id.mul continuous_const)
  have he : (∫ _x in a..b, g b) = g b := by simp [intervalIntegral.integral_const,a,b]
  change ‖g b - ∫ x in a..b, g x‖ ≤ _
  rw [← he, ← intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  let C := 2*Real.pi*|u|
  calc
    _ ≤ ∫ x in a..b, C*(b-x) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall ?_)
        ((show Continuous (fun x : ℝ => C*(b-x)) by fun_prop).intervalIntegrable _ _)
      intro x hx
      calc ‖g b-g x‖ ≤ 2*Real.pi*|b*u-x*u| := energy_model_upper_bound_aux_phaseLip _ _
           _ = _ := by rw [← sub_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hx.2)]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (f:=fun _ : ℝ => b) (g:=fun x : ℝ => x) (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
        integral_id,intervalIntegral.integral_const]
      dsimp [a,b,C]; ring

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_approx (n : ℕ) (hn : 0<n) (t : ℝ) :
    ‖energy_model_upper_bound_aux_polysum n (t/n)/(n:ℂ) - energy_model_upper_bound_aux_target t‖ ≤ Real.pi*|t|/n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let u := t/n
  let g := fun x : ℝ => energy_model_upper_bound_aux_phase (x*u)
  have hg : Continuous g := energy_model_upper_bound_aux_continuousPhase.comp (continuous_id.mul continuous_const)
  have tel := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => (k:ℝ)) (n:=n)
    (fun k _ => hg.intervalIntegrable (μ:=volume) (a:=(k:ℝ)) (b:=((k+1:ℕ):ℝ)))
  have integ : (∫ x in (0:ℝ)..n, g x) = (n:ℂ)*energy_model_upper_bound_aux_target t := by
    have sm := intervalIntegral.integral_comp_div (a:=(0:ℝ)) (b:=(n:ℝ)) (fun x : ℝ => energy_model_upper_bound_aux_phase (x*t)) hnR.ne'
    simp only [zero_div,div_self hnR.ne',energy_model_upper_bound_aux_kernelInt,Complex.real_smul,Complex.ofReal_natCast] at sm
    convert sm using 1
    apply intervalIntegral.integral_congr; intro x _
    unfold g u; congr 1; ring
  have C : ‖energy_model_upper_bound_aux_polysum n u - (n:ℂ)*energy_model_upper_bound_aux_target t‖ ≤ (n:ℝ)*(Real.pi*|u|) := by
    rw [energy_model_upper_bound_aux_rangePoly,← integ]
    simp only [Nat.cast_zero,Nat.cast_add,Nat.cast_one] at tel
    rw [← tel, ← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k _ => energy_model_upper_bound_aux_cell u k)).trans_eq (by simp))
  change ‖energy_model_upper_bound_aux_polysum n u/(n:ℂ)-energy_model_upper_bound_aux_target t‖ ≤ _
  rw [show energy_model_upper_bound_aux_polysum n u/(n:ℂ)-energy_model_upper_bound_aux_target t=(energy_model_upper_bound_aux_polysum n u-(n:ℂ)*energy_model_upper_bound_aux_target t)/(n:ℂ) by field_simp, norm_div,Complex.norm_natCast]
  rw [div_le_div_iff_of_pos_right hnR]
  apply C.trans_eq
  dsimp [u]; rw [abs_div,abs_of_pos hnR]; field_simp

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_avgNorm (n : ℕ) (hn : 0<n) (t : ℝ) : ‖energy_model_upper_bound_aux_polysum n (t/n)/(n:ℂ)‖ ≤ 1 := by
  rw [norm_div,Complex.norm_natCast, div_le_one (by exact_mod_cast hn)]
  unfold energy_model_upper_bound_aux_polysum
  exact (norm_sum_le _ _).trans (by simp [energy_model_upper_bound_aux_phaseNorm,Nat.card_Icc])

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_targetSq (t : ℝ) : (energy_model_upper_bound_aux_target t)^2 * energy_model_upper_bound_aux_phase (-t) = ((Real.sinc (Real.pi*t))^2 : ℝ) := by
  have h : energy_model_upper_bound_aux_phase (t/2)*energy_model_upper_bound_aux_phase (t/2)*energy_model_upper_bound_aux_phase (-t)=1 := by
    rw [← energy_model_upper_bound_aux_phaseAdd, ← energy_model_upper_bound_aux_phaseAdd,show t/2+t/2 + -t = 0 by ring]
    simp [energy_model_upper_bound_aux_phase]
  dsimp [energy_model_upper_bound_aux_target]; push_cast
  linear_combination (Real.sinc (Real.pi*t):ℂ)^2*h

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_scaled {𝕜 : Type*} [RCLike 𝕜] (v : ℝ → 𝕜) (d h : ℝ) (hd : d≠0) :
    (∫ x in -h..h, v (x/d)/(d:𝕜)^2) = (∫ x in -(h/d)..h/d, v x)/(d:𝕜) := by
  rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_div v hd, neg_div, RCLike.real_smul_eq_coe_mul]
  have hn : (d:𝕜)≠0 := by exact_mod_cast hd
  field_simp

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_intBound {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ → 𝕜} (ha : Continuous a) (hb : Continuous b)
    (h C : ℝ) (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hab : ∀ x, ‖a x-b x‖ ≤ C*|x|) :
    ‖(∫ x in -h..h, a x)-(∫ x in -h..h, b x)‖ ≤ 2*C*h^2 := by
  rw [← intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _)]
  have step := intervalIntegral.norm_integral_le_of_norm_le_const (a := -h) (b := h) (C := C*h)
    (f := fun x => a x-b x) (fun x hx => (hab x).trans (mul_le_mul_of_nonneg_left (by
      rw [Set.uIoc_of_le (by linarith : -h≤h)] at hx
      exact abs_le.mpr ⟨hx.1.le,hx.2⟩) hC))
  exact step.trans_eq (by rw [abs_of_nonneg (by linarith : 0 ≤ h- -h)]; ring)

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_upstream : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let _J := fun (h : ℝ) (f : ℝ → ℂ) => intervalIntegral f (-h) h MeasureTheory.volume; let Jr := fun (h : ℝ) (f : ℝ → ℝ) => intervalIntegral f (-h) h MeasureTheory.volume; let V := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β); ∀ (n : ℕ) (h : ℝ), 0<n → 0≤h → (let f := fun t : ℝ => V n (t/n)/(n:ℂ); (∀ t : ℝ, ‖f t - E (t/2)*(Real.sinc (Real.pi*t):ℂ)‖ ≤ 2*Real.pi*|t|/(n:ℝ)) ∧ |((_J (h/n) (fun β => (V n β)^2*E (-(n:ℝ)*β))).re/(n:ℝ)) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ) ∧ |Jr (h/n) (fun β => ‖V n β‖^2)/(n:ℝ) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ)) := by
  dsimp only
  intro n h hn hh
  have hr : 0 < (n:ℝ) := by exact_mod_cast hn
  let F := fun t : ℝ => energy_model_upper_bound_aux_polysum n (t/n)/(n:ℂ)
  let sqF := fun t : ℝ => (F t)^2*energy_model_upper_bound_aux_phase (-t)
  let sqG := fun t : ℝ => (((Real.sinc (Real.pi*t))^2:ℝ):ℂ)
  let M := fun t : ℝ => ‖F t‖^2
  let J := fun t : ℝ => (Real.sinc (Real.pi*t))^2
  have cF : Continuous F := (energy_model_upper_bound_aux_continuousPoly n |>.comp (continuous_id.div_const _)).div_const _
  have cSq : Continuous sqF := (cF.pow 2).mul (energy_model_upper_bound_aux_continuousPhase.comp continuous_neg)
  have cJ : Continuous J := by dsimp [J]; fun_prop
  have cG : Continuous sqG := Complex.continuous_ofReal.comp cJ
  have cM : Continuous M := cF.norm.pow 2
  have hp t : ‖F t - energy_model_upper_bound_aux_target t‖ ≤ Real.pi*|t|/n := energy_model_upper_bound_aux_approx n hn t
  have hF t : ‖F t‖ ≤ 1 := energy_model_upper_bound_aux_avgNorm n hn t
  have c : 0 ≤ 2*Real.pi/(n:ℝ) := by positivity
  have pointC t : ‖sqF t-sqG t‖ ≤ 2*Real.pi/n*|t| := by
    change ‖F t^2 * energy_model_upper_bound_aux_phase (-t) - ((J t : ℝ):ℂ)‖ ≤ _
    rw [show ((J t : ℝ):ℂ) = energy_model_upper_bound_aux_target t^2*energy_model_upper_bound_aux_phase (-t) from (energy_model_upper_bound_aux_targetSq _).symm,
        ← sub_mul,norm_mul,energy_model_upper_bound_aux_phaseNorm,mul_one, sq_sub_sq,norm_mul]
    have hs : ‖F t + energy_model_upper_bound_aux_target t‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hF t,energy_model_upper_bound_aux_targetNorm t])
    calc _ ≤ 2*(Real.pi*|t|/n) := by nlinarith [mul_le_mul hs (hp t) (norm_nonneg (F t-energy_model_upper_bound_aux_target t)) (by norm_num : (0:ℝ)≤2)]
         _ = _ := by ring
  have pointR t : ‖M t-J t‖ ≤ 2*Real.pi/n*|t| := by
    have ht : ‖energy_model_upper_bound_aux_target t‖^2 = J t := by simp [energy_model_upper_bound_aux_target,J,norm_mul,energy_model_upper_bound_aux_phaseNorm,Complex.norm_real, Real.norm_eq_abs,sq_abs]
    change ‖‖F t‖^2-J t‖ ≤ _
    rw [← ht,sq_sub_sq,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤‖F t‖+‖energy_model_upper_bound_aux_target t‖)]
    have hd := (abs_norm_sub_norm_le (F t) (energy_model_upper_bound_aux_target t)).trans (hp t)
    have hs : ‖F t‖+‖energy_model_upper_bound_aux_target t‖ ≤ 2 := by linarith [hF t,energy_model_upper_bound_aux_targetNorm t]
    calc _ ≤ 2*(Real.pi*|t|/n) := by nlinarith [mul_le_mul hs hd (abs_nonneg (‖F t‖-‖energy_model_upper_bound_aux_target t‖)) (by norm_num : (0:ℝ)≤2)]
         _ = _ := by ring
  have sc : (∫ t in -h..h, sqF t) = (∫ β in -(h/n)..h/n, energy_model_upper_bound_aux_polysum n β^2*energy_model_upper_bound_aux_phase (-(n:ℝ)*β))/(n:ℂ) := by
    convert energy_model_upper_bound_aux_scaled (fun β : ℝ => energy_model_upper_bound_aux_polysum n β^2*energy_model_upper_bound_aux_phase (-(n:ℝ)*β)) (n:ℝ) h hr.ne' using 1
    apply intervalIntegral.integral_congr
    intro t _
    have he : -(n:ℝ)*(t/n) = -t := by field_simp
    change (energy_model_upper_bound_aux_polysum n (t/n)/(n:ℂ))^2 * energy_model_upper_bound_aux_phase (-t) = (energy_model_upper_bound_aux_polysum n (t/n)^2 * energy_model_upper_bound_aux_phase (-(n:ℝ)*(t/n))) / (((n:ℝ):ℂ)^2)
    rw [he,Complex.ofReal_natCast,div_pow]
    ring
  have sr : (∫ t in -h..h, M t) = (∫ β in -(h/n)..h/n, ‖energy_model_upper_bound_aux_polysum n β‖^2)/(n:ℝ) := by
    convert energy_model_upper_bound_aux_scaled (fun β : ℝ => ‖energy_model_upper_bound_aux_polysum n β‖^2) (n:ℝ) h hr.ne' using 1
    apply intervalIntegral.integral_congr; intro t _
    simp [M,F,norm_div,Complex.norm_natCast,div_pow]
  have hG : (∫ t in -h..h, sqG t) = ((∫ t in -h..h, J t):ℝ) := intervalIntegral.integral_ofReal
  refine ⟨fun t => (hp t).trans (by have := abs_nonneg t; gcongr <;> linarith [Real.pi_pos]),?_,?_⟩
  · have hc := energy_model_upper_bound_aux_intBound cSq cG h (2*Real.pi/n) hh c pointC
    have hl := (Complex.abs_re_le_norm _).trans hc
    rw [sc,hG,Complex.sub_re,Complex.ofReal_re] at hl
    have hre (z : ℂ) : (z/(n:ℂ)).re = z.re/n := by exact Complex.div_ofReal_re z (n:ℝ)
    rw [hre] at hl
    exact hl.trans_eq (by ring)
  · have hl := energy_model_upper_bound_aux_intBound cM cJ h (2*Real.pi/n) hh c pointR
    rw [sr,Real.norm_eq_abs] at hl
    exact hl.trans_eq (by ring)

open MeasureTheory intervalIntegral in
open scoped Interval in
set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_raw (n : ℕ) (h : ℝ) (hn : 0 < n) (hh : 0 ≤ h) :
    |intervalIntegral (fun β => ‖FixedModelBoundsBlueprint.V n β‖ ^ 2) (-(h / (n : ℝ)))
        (h / (n : ℝ)) MeasureTheory.volume / (n : ℝ) -
      intervalIntegral (fun t => Real.sinc (Real.pi * t) ^ 2) (-h) h
        MeasureTheory.volume| ≤
      4 * Real.pi * h ^ 2 / (n : ℝ) := by
  have h3 := (energy_model_upper_bound_aux_upstream n h hn hh).2.2
  simpa only [FixedModelBoundsBlueprint.V, FixedModelBoundsBlueprint.E] using h3

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_T_bound (n q : ℕ) (hn : 0 < n) (hq : 1 ≤ q) :
    |FixedModelBoundsBlueprint.T n q -
        FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ))| ≤
      4 * Real.pi * ((105 : ℝ) / (q : ℝ)) ^ 2 / (n : ℝ) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hraw := energy_model_upper_bound_aux_raw n ((105 : ℝ) / (q : ℝ)) hn (by positivity)
  have hrw : ((105 : ℝ) / (q : ℝ)) / (n : ℝ) = FixedModelBoundsBlueprint.H n q := by
    simp only [FixedModelBoundsBlueprint.H]
    ring
  rw [hrw] at hraw
  simpa only [FixedModelBoundsBlueprint.T, FixedModelBoundsBlueprint.K,
    FixedModelBoundsBlueprint.Jr] using hraw

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_coeff_nonneg (q : ℕ) :
    0 ≤ FixedModelBoundsBlueprint.energyCoeff q := by
  unfold FixedModelBoundsBlueprint.energyCoeff
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound_aux_T_le (n q : ℕ) (hn : 0 < n) (hq : 1 ≤ q) :
    FixedModelBoundsBlueprint.T n q ≤
      1 + 4 * Real.pi * 11025 / (n : ℝ) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqR0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le one_pos hqR
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hK : FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)) ≤ 1 :=
    (energy_model_upper_bound_aux_sinc_mass_bounds ((105 : ℝ) / (q : ℝ))
      (by positivity)).2.1
  have hT := energy_model_upper_bound_aux_T_bound n q hn hq
  have h105 : (105 : ℝ) / (q : ℝ) ≤ 105 := by
    rw [div_le_iff₀ hqR0]
    nlinarith
  have hsq : ((105 : ℝ) / (q : ℝ)) ^ 2 ≤ (11025 : ℝ) := by
    calc ((105 : ℝ) / (q : ℝ)) ^ 2 ≤ (105 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h105 2
      _ = 11025 := by norm_num
  have hpi : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  have hmain : 4 * Real.pi * ((105 : ℝ) / (q : ℝ)) ^ 2 / (n : ℝ) ≤
      4 * Real.pi * 11025 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact mul_le_mul_of_nonneg_left hsq hpi
  have h1 : FixedModelBoundsBlueprint.T n q -
      FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)) ≤
      4 * Real.pi * ((105 : ℝ) / (q : ℝ)) ^ 2 / (n : ℝ) := by
    have h2 := le_abs_self (FixedModelBoundsBlueprint.T n q -
      FixedModelBoundsBlueprint.K ((105 : ℝ) / (q : ℝ)))
    linarith [hT]
  linarith

set_option maxRecDepth 100000 in
theorem energy_model_upper_bound
    (n : ℕ) (hn : 4000000000000000000 ≤ n) :
    FixedModelBoundsBlueprint.B n < 6 * (n : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnR4 : (4000000000000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hε : 4 * Real.pi * 11025 / (n : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hnR]
    nlinarith [hnR4]
  have hε0 : (0 : ℝ) ≤ 4 * Real.pi * 11025 / (n : ℝ) := by positivity
  have hpos : (0 : ℝ) < 1 + 4 * Real.pi * 11025 / (n : ℝ) := by linarith
  have hε' : 1 + 4 * Real.pi * 11025 / (n : ℝ) ≤ 1 + (1 / 1000 : ℝ) := by linarith
  rw [← div_lt_iff₀ hnR, energy_model_upper_bound_aux_energy_model_normal_form n]
  calc (∑ q ∈ FixedModelBoundsBlueprint.Q,
          FixedModelBoundsBlueprint.energyCoeff q *
            FixedModelBoundsBlueprint.T n q)
      ≤ ∑ q ∈ FixedModelBoundsBlueprint.Q,
          FixedModelBoundsBlueprint.energyCoeff q *
            (1 + 4 * Real.pi * 11025 / (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        exact mul_le_mul_of_nonneg_left
          (energy_model_upper_bound_aux_T_le n q hn0 hq1)
          (energy_model_upper_bound_aux_coeff_nonneg q)
    _ = (∑ q ∈ FixedModelBoundsBlueprint.Q,
          FixedModelBoundsBlueprint.energyCoeff q) *
          (1 + 4 * Real.pi * 11025 / (n : ℝ)) := by
        rw [Finset.sum_mul]
    _ < (5983 / 1000 : ℝ) * (1 + 4 * Real.pi * 11025 / (n : ℝ)) :=
        mul_lt_mul_of_pos_right
          energy_model_upper_bound_aux_reciprocal_totient_sum hpos
    _ ≤ (5983 / 1000 : ℝ) * (1 + (1 / 1000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hε' (by norm_num)
    _ < 6 := by norm_num

set_option maxRecDepth 100000 in
theorem Conjectures.Goldbach.FiniteMajorFixedModelBounds : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let _J := fun (h : ℝ) (f : ℝ → ℂ) => intervalIntegral f (-h) h MeasureTheory.volume; let Jr := fun (h : ℝ) (f : ℝ → ℝ) => intervalIntegral f (-h) h MeasureTheory.volume; let V := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β); let M := fun (n q : ℕ) (β : ℝ) => ((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*V n β; let H := fun (n q : ℕ) => (105:ℝ)/((q:ℝ)*(n:ℝ)); let Q := Finset.Icc (1:ℕ) 105; let A := fun (q : ℕ) => (Finset.range q).filter (fun a => Nat.Coprime a q); let B := fun (n : ℕ) => ∑ q ∈ Q, ((A q).card:ℝ) * Jr (H n q) (fun β => ‖M n q β‖^2); let C := fun (n : ℕ) => ∑ q ∈ Q, ∑ a ∈ A q, (_J (H n q) (fun β => (M n q β)^2*E (-(n:ℝ)*((a:ℝ)/q+β)))).re; ∀ n : ℕ, 4000000000000000000≤n → 30 ∣ n → (7/2:ℝ)*(n:ℝ) < C n ∧ B n < 6*(n:ℝ) := by
  simp only
  intro n hn hdiv
  constructor
  · simpa [FixedModelBoundsBlueprint.C, FixedModelBoundsBlueprint.E,
      FixedModelBoundsBlueprint.J, FixedModelBoundsBlueprint.V,
      FixedModelBoundsBlueprint.M, FixedModelBoundsBlueprint.H,
      FixedModelBoundsBlueprint.Q, FixedModelBoundsBlueprint.A] using
      signed_model_lower_bound n hn hdiv
  · simpa [FixedModelBoundsBlueprint.B, FixedModelBoundsBlueprint.E,
      FixedModelBoundsBlueprint.Jr, FixedModelBoundsBlueprint.V,
      FixedModelBoundsBlueprint.M, FixedModelBoundsBlueprint.H,
      FixedModelBoundsBlueprint.Q, FixedModelBoundsBlueprint.A] using
      energy_model_upper_bound n hn
