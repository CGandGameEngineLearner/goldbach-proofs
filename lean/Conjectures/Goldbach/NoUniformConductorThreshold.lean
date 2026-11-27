import Mathlib

open scoped BigOperators
open MeasureTheory

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

noncomputable section

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def numerators (q : ℕ) : Finset ℕ :=
  (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)

def center (q a : ℕ) : ℝ := (a : ℝ) / (q : ℝ)

def width (n q : ℕ) : ℝ := (Q n : ℝ) / ((q : ℝ) * (n : ℝ))

def K (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * t)

def unitMean (q a : ℕ) : ℂ :=
  (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), E ((b : ℝ) * center q a)) /
    (q.totient : ℂ)

def finiteFourier (q a : ℕ) (v : ℕ → ℝ) : ℂ :=
  ∑ b ∈ Finset.range q, (v b : ℂ) * E ((b : ℝ) * center q a)

def secondary (d : ℕ) (c : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (m q b : ℕ) : ℝ :=
  if d ∣ q then c q b * ψ m / (q.totient : ℝ) else 0

def profileSize (n d : ℕ) (c : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (q a : ℕ) : ℝ :=
  (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩
    (fun m => ‖finiteFourier q a (secondary d c ψ m q)‖)

def amplified (n : ℕ) (D β : ℝ) : ℝ := D * (1 + 2 * Real.pi * n * |β|)

def prefixCost (n q a : ℕ) (D β : ℝ) : ℝ :=
  amplified n D β * (2 * ‖unitMean q a * K n β‖ + amplified n D β)

def leftEnd (n q a : ℕ) : ℝ := max (center q a - width n q) 0 - center q a

def rightEnd (n q a : ℕ) : ℝ := min (center q a + width n q) 1 - center q a

def exceptionalBudget (n d : ℕ) (D : ℕ → ℕ → ℝ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 (Q n)).filter (fun q => d ∣ q),
    ∑ a ∈ numerators q,
      intervalIntegral (prefixCost n q a (D q a)) (leftEnd n q a) (rightEnd n q a)
        MeasureTheory.volume

end

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

noncomputable section

lemma arithmetic (Q₀ : ℕ) :
    ∃ k d n : ℕ,
      200 ≤ k ∧ Nat.Prime d ∧ Q₀ ≤ d ∧ d ≤ k ^ 2 ∧ k ^ 2 < 2 * d ∧
      n = 2 ^ k ∧ 100000000000 < n ∧ Even n ∧
      Nat.log 2 (n + 2) = k := by
  classical
  let k := 2 * (Q₀ + 100)
  have hk200 : 200 ≤ k := by dsimp [k]; omega
  have hkpos : 0 < k := by omega
  have hkeven : Even k := by dsimp [k]; exact even_two_mul (Q₀ + 100)
  let m := k ^ 2 / 2
  have hmpos : m ≠ 0 := by
    dsimp [m]
    exact ne_of_gt (Nat.div_pos (by nlinarith [hk200]) (by norm_num))
  obtain ⟨d, hdprime, hdgt, hdle⟩ := Nat.bertrand m hmpos
  have hk2eq : 2 * m = k ^ 2 := by
    have hdvd : 2 ∣ k ^ 2 := by
      rcases hkeven with ⟨t, ht⟩
      use 2 * t ^ 2
      rw [ht]
      ring
    dsimp [m]
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvd
  have hmQ0 : Q₀ ≤ m := by
    have hkQ0 : Q₀ ≤ k := by dsimp [k]; omega
    have hk_le_m : k ≤ m := by
      dsimp [m]
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      nlinarith [hk200]
    omega
  refine ⟨k, d, 2 ^ k, hk200, hdprime, by omega, by omega, by omega,
    rfl, ?_, ?_, ?_⟩
  · have hk37 : 37 ≤ k := by omega
    have hpow : 2 ^ 37 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk37
    have hbase : (100000000000 : ℕ) < 2 ^ 37 := by norm_num
    omega
  · have hk1 : 1 ≤ k := by omega
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk1]
        _ = 2 ^ (k - 1) * 2 := pow_succ 2 (k - 1)
        _ = 2 * 2 ^ (k - 1) := by ring
    refine ⟨2 ^ (k - 1), ?_⟩
    omega
  · have h2 : 2 < 2 ^ k := by
      have hk2 : 2 ≤ k := by omega
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    have hlt : 2 ^ k + 2 < 2 ^ (k + 1) := by
      have hlt' : 2 ^ k + 2 < 2 * 2 ^ k := by nlinarith
      simpa [pow_succ, Nat.mul_comm] using hlt'
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt

end

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

lemma sq_lt_two_pow (k : ℕ) (hk : 5 ≤ k) : k ^ 2 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have h2k1 : 2 * k + 1 ≤ k ^ 2 := by nlinarith
      have hstep : (k + 1) ^ 2 < 2 ^ (k + 1) := by
        conv_rhs => rw [pow_succ]
        have hsq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
        rw [hsq]
        nlinarith [ih, h2k1]
      simpa [Nat.succ_eq_add_one] using hstep

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

noncomputable section

def delta (d : ℕ) : ℕ → ℝ := fun b => if b = 0 then Real.sqrt d else 0

lemma finiteFourier_const_mul (q a : ℕ) (c : ℕ → ℝ) (s : ℝ) :
    finiteFourier q a (fun b => c b * s) = finiteFourier q a c * s := by
  unfold finiteFourier
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  push_cast
  ring

lemma finiteFourier_delta (d a : ℕ) (hd : 0 < d) :
    finiteFourier d a (delta d) = (Real.sqrt d : ℂ) := by
  unfold finiteFourier delta
  rw [Finset.sum_eq_single 0]
  · simp [E, center]
  · intro b hb hne
    simp [hne]
  · intro hzero
    simp at hzero
    omega

lemma profile_lower (n d a : ℕ) (hd : 0 < d) (hprime : Nat.Prime d) (β : ℝ) :
    Real.sqrt d * ((n + 1 : ℝ) ^ β) / ((d - 1 : ℕ) : ℝ) ≤
      profileSize n d
        (fun q b => if q = d then delta d b else 0)
        (fun m => (m : ℝ) ^ β) d a := by
  have hmem : n + 1 ∈ Finset.range (n + 2) :=
    Finset.mem_range.mpr (by omega)
  have hle := Finset.le_sup'
    (fun m => ‖finiteFourier d a
      (secondary d (fun q b => if q = d then delta d b else 0)
        (fun m => (m : ℝ) ^ β) m d)‖) hmem
  have hφ : (d.totient : ℝ) = (d - 1 : ℕ) := by
    rw [Nat.totient_prime hprime]
  have hsec : secondary d (fun q b => if q = d then delta d b else 0)
      (fun m => (m : ℝ) ^ β) (n + 1) d =
      (fun b => delta d b * ((n + 1 : ℝ) ^ β / ((d - 1 : ℕ) : ℝ))) := by
    funext b
    by_cases hb : b = 0
    · simp [secondary, hφ, delta, hb, mul_div_assoc]
    · simp [secondary, hφ, delta, hb]
  have hfin : finiteFourier d a
      (secondary d (fun q b => if q = d then delta d b else 0)
        (fun m => (m : ℝ) ^ β) (n + 1) d) =
      (Real.sqrt d : ℂ) * (((n + 1 : ℝ) ^ β / ((d - 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [hsec, finiteFourier_const_mul, finiteFourier_delta d a hd]
  rw [hfin] at hle
  have hs : (0 : ℝ) ≤ (n + 1 : ℝ) ^ β := Real.rpow_nonneg (by positivity) β
  have hd1 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
    have : 1 < d := hprime.one_lt
    exact_mod_cast (Nat.sub_pos_of_lt this)
  have hnorm : ‖(Real.sqrt d : ℂ) *
      (((n + 1 : ℝ) ^ β / ((d - 1 : ℕ) : ℝ) : ℝ) : ℂ)‖ =
      Real.sqrt d * ((n + 1 : ℝ) ^ β / ((d - 1 : ℕ) : ℝ)) := by
    have hdiv : 0 ≤ (n + 1 : ℝ) ^ β / ((d - 1 : ℕ) : ℝ) :=
      div_nonneg hs hd1.le
    have h1 : ‖(Real.sqrt d : ℂ)‖ = Real.sqrt d := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg d)]
    have h2 : ‖(((n + 1 : ℝ) ^ β / ((d - 1 : ℕ) : ℝ) : ℝ) : ℂ)‖ =
        (n + 1 : ℝ) ^ β / ((d - 1 : ℕ) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdiv]
    rw [norm_mul, h1, h2]
  rw [hnorm] at hle
  simpa [profileSize, mul_div_assoc] using hle

end

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

lemma numerators_card_ge (p : ℕ) (hp : Nat.Prime p) :
    p - 1 ≤ (numerators p).card := by
  have hsub : Finset.Icc 1 (p - 1) ⊆ numerators p := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [numerators, Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · have hlt : a < p := by omega
      have hpos : 0 < a := by omega
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (by
        intro hdvd
        have := Nat.le_of_dvd hpos hdvd
        omega)
  have hcard : (Finset.Icc 1 (p - 1)).card = p - 1 := by simp
  rw [← hcard]
  exact Finset.card_le_card hsub

lemma mem_numerators_bounds {p a : ℕ} (hp : Nat.Prime p)
    (ha : a ∈ numerators p) : 1 ≤ a ∧ a ≤ p - 1 := by
  rw [numerators, Finset.mem_filter, Finset.mem_range] at ha
  rcases ha with ⟨harange, hcop⟩
  have hap : a ≤ p := by omega
  have hne0 : a ≠ 0 := by
    intro h
    subst a
    simp at hcop
    exact hp.ne_one hcop
  have hneP : a ≠ p := by
    intro h
    subst a
    have : p ∣ p := dvd_rfl
    have hnot : ¬ p ∣ p := (Nat.Prime.coprime_iff_not_dvd hp).mp (by simpa using hcop)
    exact hnot this
  omega

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

lemma width_lt_inv (n d k : ℕ) (hQ : Q n = k ^ 2) (hd : 0 < d) (hn : 0 < n)
    (hkn : k ^ 2 < n) : width n d < 1 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hknR : ((k ^ 2 : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hkn
  unfold width
  rw [hQ]
  field_simp [hd0.ne', hn0.ne']
  nlinarith

lemma endpoints_eq (n d k a : ℕ) (hQ : Q n = k ^ 2) (hd : 0 < d)
    (hprime : Nat.Prime d) (hn : 0 < n) (hkn : k ^ 2 < n) (ha : a ∈ numerators d) :
    leftEnd n d a = -width n d ∧ rightEnd n d a = width n d := by
  have hwlt := width_lt_inv n d k hQ hd hn hkn
  have hw0 : 0 ≤ width n d := by
    unfold width
    positivity
  obtain ⟨ha1, ha2⟩ := mem_numerators_bounds hprime ha
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 : ℝ) / (d : ℝ) ≤ (a : ℝ) / (d : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha1) hd0.le
  have h2 : (a : ℝ) / (d : ℝ) ≤ ((d - 1 : ℕ) : ℝ) / (d : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha2) hd0.le
  have h3 : (((d - 1 : ℕ) : ℝ) / (d : ℝ) + 1 / (d : ℝ) = 1) := by
    field_simp
    have hd1 : 1 ≤ d := hprime.one_lt.le
    rw [Nat.cast_sub hd1]
    ring
  have hleft : width n d < (a : ℝ) / (d : ℝ) := by linarith
  have hright : (a : ℝ) / (d : ℝ) + width n d < 1 := by linarith
  unfold leftEnd rightEnd center
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  simp

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

lemma prefixCost_ge (n q a : ℕ) (D D0 β : ℝ) (hD0 : 0 ≤ D0) (hD : D0 ≤ D) :
    D0 ^ 2 ≤ prefixCost n q a D β := by
  have hfac : 1 ≤ 1 + 2 * Real.pi * (n : ℝ) * |β| := by
    have : 0 ≤ 2 * Real.pi * (n : ℝ) * |β| := by positivity
    linarith
  have hDnonneg : 0 ≤ D := le_trans hD0 hD
  have hA0 : 0 ≤ amplified n D β := by
    unfold amplified
    exact mul_nonneg hDnonneg (by linarith)
  have hAle : D0 ≤ amplified n D β := by
    unfold amplified
    calc
      D0 ≤ D := hD
      _ ≤ D * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
        exact le_mul_of_one_le_right hDnonneg hfac
  have hAA : (amplified n D β) ^ 2 ≤ prefixCost n q a D β := by
    unfold prefixCost
    have hz : 0 ≤ 2 * ‖unitMean q a * K n β‖ := by positivity
    calc
      (amplified n D β) ^ 2 = amplified n D β * amplified n D β := by ring
      _ ≤ amplified n D β * (2 * ‖unitMean q a * K n β‖ + amplified n D β) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hA0
  exact le_trans (pow_le_pow_left₀ hD0 hAle 2) hAA

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

lemma filter_multiples_eq (n d : ℕ) (hd : 0 < d) (hdQ : d ≤ Q n) (hQ2 : Q n < 2 * d) :
    (Finset.Icc 1 (Q n)).filter (fun q => d ∣ q) = {d} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hdQ⟩, dvd_rfl⟩
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    rcases hq with ⟨⟨hq1, hqQ⟩, hdvd⟩
    rcases hdvd with ⟨m, rfl⟩
    have hmpos : 0 < m := by
      by_contra hm
      have : m = 0 := by omega
      subst m
      omega
    have hm_lt : m < 2 := by
      by_contra hm
      have hm2 : 2 ≤ m := by omega
      have h1 : d * 2 ≤ d * m := Nat.mul_le_mul_left d hm2
      have h1' : 2 * d ≤ d * m := by simpa [Nat.mul_comm] using h1
      omega
    have hm1 : m = 1 := by omega
    subst m
    omega

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

noncomputable def Dzero (n d : ℕ) (β : ℝ) : ℝ :=
  Real.sqrt d * ((n + 1 : ℝ) ^ β) / ((d - 1 : ℕ) : ℝ)

lemma Dzero_nonneg (n d : ℕ) (β : ℝ) : 0 ≤ Dzero n d β := by
  unfold Dzero
  positivity

set_option maxHeartbeats 4000000 in
lemma term_lower (n d k a : ℕ) (β D : ℝ) (hQ : Q n = k ^ 2) (hd : 0 < d)
    (hprime : Nat.Prime d) (hn : 0 < n) (hkn : k ^ 2 < n)
    (ha : a ∈ numerators d) (hD0 : 0 ≤ Dzero n d β)
    (hD : Dzero n d β ≤ D) :
    2 * width n d * (Dzero n d β) ^ 2 ≤
      intervalIntegral (prefixCost n d a D) (leftEnd n d a) (rightEnd n d a)
        MeasureTheory.volume := by
  have hw0 : 0 ≤ width n d := by
    unfold width
    positivity
  have hleft : leftEnd n d a = -width n d := (endpoints_eq n d k a hQ hd hprime hn hkn ha).1
  have hright : rightEnd n d a = width n d := (endpoints_eq n d k a hQ hd hprime hn hkn ha).2
  have hE : Continuous E := by
    unfold E
    fun_prop
  have hK : Continuous (K n) := by
    unfold K
    exact continuous_finsetSum (Finset.range (n + 1)) (fun k _ =>
      hE.comp (by fun_prop))
  let A : ℝ → ℝ := fun v => D * (1 + 2 * Real.pi * (n : ℝ) * |v|)
  have hA : Continuous A := by
    dsimp [A]
    fun_prop
  have hnorm : Continuous (fun v : ℝ => ‖unitMean d a * K n v‖) :=
    continuous_norm.comp (continuous_const.mul hK)
  have hZ : Continuous (fun v : ℝ => 2 * ‖unitMean d a * K n v‖ + A v) :=
    (continuous_const.mul hnorm).add hA
  have hcont : Continuous (fun v : ℝ => prefixCost n d a D v) := by
    change Continuous (fun v : ℝ =>
      A v * (2 * ‖unitMean d a * K n v‖ + A v))
    exact hA.mul hZ
  have hmono : intervalIntegral (fun _ : ℝ => (Dzero n d β) ^ 2)
      (-width n d) (width n d) MeasureTheory.volume ≤
      intervalIntegral (fun v : ℝ => prefixCost n d a D v)
        (-width n d) (width n d) MeasureTheory.volume := by
    apply intervalIntegral.integral_mono_on (by linarith : -width n d ≤ width n d)
    · exact intervalIntegrable_const
    · exact hcont.intervalIntegrable _ _
    · intro v hv
      have hfac : 1 ≤ 1 + 2 * Real.pi * (n : ℝ) * |v| := by
        have : 0 ≤ 2 * Real.pi * (n : ℝ) * |v| := by positivity
        linarith
      have hDnonneg : 0 ≤ D := le_trans hD0 hD
      have hA0 : 0 ≤ amplified n D v := by
        unfold amplified
        exact mul_nonneg hDnonneg (by linarith)
      have hAle : Dzero n d β ≤ amplified n D v := by
        unfold amplified
        calc
          Dzero n d β ≤ D := hD
          _ ≤ D * (1 + 2 * Real.pi * (n : ℝ) * |v|) := by
            exact le_mul_of_one_le_right hDnonneg hfac
      have hAA : (amplified n D v) ^ 2 ≤ prefixCost n d a D v := by
        unfold prefixCost
        have hz : 0 ≤ 2 * ‖unitMean d a * K n v‖ := by positivity
        calc
          (amplified n D v) ^ 2 = amplified n D v * amplified n D v := by ring
          _ ≤ amplified n D v *
              (2 * ‖unitMean d a * K n v‖ + amplified n D v) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hA0
      exact le_trans (pow_le_pow_left₀ hD0 hAle 2) hAA
  have hconst : intervalIntegral (fun _ : ℝ => (Dzero n d β) ^ 2)
      (-width n d) (width n d) MeasureTheory.volume =
      2 * width n d * (Dzero n d β) ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hleft, hright]
  calc
    2 * width n d * (Dzero n d β) ^ 2 =
        intervalIntegral (fun _ : ℝ => (Dzero n d β) ^ 2)
          (-width n d) (width n d) MeasureTheory.volume := hconst.symm
    _ ≤ _ := hmono

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

set_option maxHeartbeats 1000000 in
lemma budget_lower (n d k : ℕ) (β : ℝ) (hQ : Q n = k ^ 2) (hd : 0 < d)
    (hprime : Nat.Prime d) (hn : 0 < n) (hkn : k ^ 2 < n)
    (hdQ : d ≤ Q n) (hQ2 : Q n < 2 * d)
    (hbeta : ((n + 1 : ℝ) ^ 2) / 2 ≤ (n + 1 : ℝ) ^ (2 * β)) :
    (n : ℝ) / 288 <
      exceptionalBudget n d
        (profileSize n d
          (fun q b => if q = d then delta d b else 0)
          (fun m => (m : ℝ) ^ β)) := by
  let c : ℕ → ℕ → ℝ := fun q b => if q = d then delta d b else 0
  let ψ : ℕ → ℝ := fun m => (m : ℝ) ^ β
  let D : ℕ → ℕ → ℝ := profileSize n d c ψ
  let C : ℝ := 2 * width n d * (Dzero n d β) ^ 2
  have hD0 : 0 ≤ Dzero n d β := Dzero_nonneg n d β
  have hD : ∀ a ∈ numerators d, Dzero n d β ≤ D d a := by
    intro a ha
    simpa [D, c, ψ, Dzero] using profile_lower n d a hd hprime β
  have hterm : ∀ a ∈ numerators d, C ≤
      intervalIntegral (prefixCost n d a (D d a)) (leftEnd n d a) (rightEnd n d a)
        MeasureTheory.volume := by
    intro a ha
    exact term_lower n d k a β (D d a) hQ hd hprime hn hkn ha hD0 (hD a ha)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    have hw : 0 ≤ width n d := by unfold width; positivity
    positivity
  have hsum : ((d - 1 : ℕ) : ℝ) * C ≤
      ∑ a ∈ numerators d, intervalIntegral
        (prefixCost n d a (D d a)) (leftEnd n d a) (rightEnd n d a)
        MeasureTheory.volume := by
    calc
      ((d - 1 : ℕ) : ℝ) * C ≤ ((numerators d).card : ℝ) * C := by
        gcongr
        exact_mod_cast numerators_card_ge d hprime
      _ = ∑ a ∈ numerators d, C := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        exact Finset.sum_le_sum hterm
  have hBudget : exceptionalBudget n d D =
      ∑ a ∈ numerators d, intervalIntegral
        (prefixCost n d a (D d a)) (leftEnd n d a) (rightEnd n d a)
        MeasureTheory.volume := by
    unfold exceptionalBudget
    rw [filter_multiples_eq n d hd hdQ hQ2]
    simp [D]
  have hsum' : ((d - 1 : ℕ) : ℝ) * C ≤ exceptionalBudget n d D := by
    rw [hBudget]
    exact hsum
  have hC_lower : (n : ℝ) / 288 < ((d - 1 : ℕ) : ℝ) * C := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hd1pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
      have : 1 < d := hprime.one_lt
      exact_mod_cast (Nat.sub_pos_of_lt this)
    have hdle : ((d - 1 : ℕ) : ℝ) ≤ (k ^ 2 : ℕ) := by
      have hdk : d ≤ k ^ 2 := by
        calc
          d ≤ Q n := hdQ
          _ = k ^ 2 := hQ
      exact_mod_cast (by omega : d - 1 ≤ k ^ 2)
    have hpow2 : ((n + 1 : ℝ) ^ β) ^ 2 = (n + 1 : ℝ) ^ (2 * β) := by
      calc
        ((n + 1 : ℝ) ^ β) ^ 2 = (n + 1 : ℝ) ^ β * (n + 1 : ℝ) ^ β := by ring
        _ = (n + 1 : ℝ) ^ (β + β) := (Real.rpow_add (by positivity) β β).symm
        _ = (n + 1 : ℝ) ^ (2 * β) := by congr 1; ring
    have hD0sq : (Dzero n d β) ^ 2 =
        (d : ℝ) * (n + 1 : ℝ) ^ (2 * β) / (((d - 1 : ℕ) : ℝ) ^ 2) := by
      unfold Dzero
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d), hpow2]
    have hwidth : width n d = (k ^ 2 : ℕ) / ((d : ℝ) * (n : ℝ)) := by
      unfold width
      rw [hQ]
    dsimp [C]
    rw [hwidth, hD0sq]
    have hkposNat : 0 < k ^ 2 := by
      have : 0 < Q n := lt_of_lt_of_le hd hdQ
      simpa [hQ] using this
    have hkpos : (0 : ℝ) < (k ^ 2 : ℕ) := by exact_mod_cast hkposNat
    field_simp [hd0.ne', hn0.ne', hd1pos.ne', hkpos.ne']
    have hbeta' := hbeta
    nlinarith

  exact hC_lower.trans_le hsum'

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

lemma rpow_beta_lower (k : ℕ) (hk : 5 ≤ k) :
    (((2 ^ k + 1 : ℕ) : ℝ) ^ 2) / 2 ≤
      (((2 ^ k + 1 : ℕ) : ℝ)) ^ (2 * (1 - 1 / (4 * (k : ℝ)))) := by
  let a : ℝ := ((2 ^ k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hexp : 2 * (1 - 1 / (4 * (k : ℝ))) = 2 - 1 / (2 * (k : ℝ)) := by
    field_simp [hkpos.ne']
    ring
  rw [hexp]
  rw [Real.rpow_sub ha]
  have hdenpos : 0 < a ^ (1 / (2 * (k : ℝ))) := by positivity
  have ha_le : a ≤ (2 : ℝ) ^ (k + 1 : ℕ) := by
    dsimp [a]
    have hk1 : 1 ≤ 2 ^ k := by
      have : 2 ^ 0 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega : 0 ≤ k)
      simpa using this
    have : (2 : ℝ) ^ (k + 1 : ℕ) = 2 * (2 : ℝ) ^ k := by
      rw [pow_succ]
      ring
    rw [this]
    have hkR : (1 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hk1
    norm_num
    nlinarith
  have hden_le : a ^ (1 / (2 * (k : ℝ))) ≤ 2 := by
    have he : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) := by positivity
    calc
      a ^ (1 / (2 * (k : ℝ))) ≤ ((2 : ℝ) ^ (k + 1 : ℕ)) ^ (1 / (2 * (k : ℝ))) := by
        exact Real.rpow_le_rpow ha.le ha_le he
      _ = (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * (1 / (2 * (k : ℝ)))) := by
        rw [← Real.rpow_natCast (2 : ℝ) (k + 1), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        have : (((k + 1 : ℕ) : ℝ) * (1 / (2 * (k : ℝ)))) ≤ 1 := by
          rw [mul_one_div]
          apply (div_le_one (by positivity : (0 : ℝ) < 2 * (k : ℝ))).mpr
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
          push_cast
          nlinarith
        exact this
      _ = 2 := by rw [Real.rpow_one]
  have hmain : a ^ 2 / 2 ≤ a ^ 2 / a ^ (1 / (2 * (k : ℝ))) := by
    apply div_le_div_of_nonneg_left (sq_nonneg a) hdenpos hden_le
  simpa [a, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

namespace Conjectures.Goldbach

open Conjectures.Goldbach.NoUniformConductorThreshold_aux

theorem NoUniformConductorThreshold :
    ∀ Q₀ : ℕ, ∃ (d n : ℕ) (c : ℕ → ℕ → ℝ) (β : ℝ),
      Nat.Prime d ∧ Q₀ ≤ d ∧ d ≤ Q n ∧ 100000000000 < n ∧ Even n ∧
      0 < β ∧ β < 1 ∧ (∀ m : ℕ, m ≤ n + 1 → |(m : ℝ) ^ β| ≤ m) ∧
      (∀ q ∈ Finset.Icc 1 (Q n), d ∣ q → ∀ a ∈ numerators q,
        ‖finiteFourier q a (c q)‖ ≤ Real.sqrt (d : ℝ)) ∧
      (n : ℝ) / 288 <
        exceptionalBudget n d (profileSize n d c (fun m => (m : ℝ) ^ β)) := by
  intro Q₀
  obtain ⟨k, d, n, hk200, hdprime, hQ0d, hdk2, hk2d, hn, hnbig, hneven, hlog⟩ :=
    arithmetic Q₀
  subst hn
  have hd : 0 < d := hdprime.pos
  have hnpos : 0 < 2 ^ k := by positivity
  have hQ : Q (2 ^ k) = k ^ 2 := by
    unfold Q
    rw [hlog]
  have hkn : k ^ 2 < 2 ^ k := sq_lt_two_pow k (by omega)
  let β : ℝ := 1 - 1 / (4 * (k : ℝ))
  let c : ℕ → ℕ → ℝ := fun q b => if q = d then delta d b else 0
  have h4k : (0 : ℝ) < 4 * (k : ℝ) := by positivity
  have hβpos : 0 < β := by
    dsimp [β]
    rw [sub_pos, div_lt_one h4k]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    nlinarith
  have hβlt : β < 1 := by
    dsimp [β]
    have : 0 < 1 / (4 * (k : ℝ)) := by positivity
    linarith
  have hbeta : ((((2 ^ k : ℕ) : ℝ) + 1) ^ 2) / 2 ≤
      (((2 ^ k : ℕ) : ℝ) + 1) ^ (2 * β) := by
    have h := rpow_beta_lower k (by omega : 5 ≤ k)
    simpa [β, Nat.cast_add, Nat.cast_one] using h
  have hbudget : (((2 ^ k : ℕ) : ℝ)) / 288 <
      exceptionalBudget (2 ^ k) d
        (profileSize (2 ^ k) d c (fun m => (m : ℝ) ^ β)) := by
    exact budget_lower (2 ^ k) d k β hQ hd hdprime hnpos hkn
      (by rw [hQ]; exact hdk2) (by rw [hQ]; exact hk2d) hbeta
  refine ⟨d, 2 ^ k, c, β, hdprime, hQ0d, ?_, hnbig, hneven, hβpos, hβlt, ?_, ?_, ?_⟩
  · rw [hQ]
    exact hdk2
  · intro m hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst m
      have hβne : β ≠ 0 := ne_of_gt hβpos
      simp [Real.zero_rpow hβne]
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
      have hnonneg : 0 ≤ (m : ℝ) ^ β := Real.rpow_nonneg (by positivity) β
      rw [abs_of_nonneg hnonneg]
      calc
        (m : ℝ) ^ β ≤ (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hm1 hβlt.le
        _ = (m : ℝ) := Real.rpow_one _
  · intro q hq hdvd a ha
    rw [Finset.mem_Icc] at hq
    obtain ⟨hq1, hqQ⟩ := hq
    rw [hQ] at hqQ
    have hqeq : q = d := by
      rcases hdvd with ⟨t, rfl⟩
      have htpos : 0 < t := by
        by_contra ht0
        have ht0' : t = 0 := by omega
        subst t
        simp at hq1
      have ht1 : t = 1 := by
        by_contra ht1
        have ht2 : 2 ≤ t := by omega
        have h1 : d * 2 ≤ d * t := Nat.mul_le_mul_left d ht2
        have h1' : 2 * d ≤ d * t := by simpa [Nat.mul_comm] using h1
        omega
      rw [ht1, Nat.mul_one]
    subst q
    have hc : c d = delta d := by
      funext b
      simp [c]
    rw [hc, finiteFourier_delta d a hd]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  · exact hbudget

end Conjectures.Goldbach
