import Mathlib

open Finset
open scoped BigOperators Interval
open ArithmeticFunction MeasureTheory

namespace Conjectures.Goldbach.FiniteMajorBmorConditionalEnergyAux


open scoped BigOperators


private theorem abelTwo :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let F := fun (q a n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, (((if k % q=a % q then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); ∀ (q a n t : ℕ) (β : ℝ), 0 < q → t ≤ n → ‖F q a n β‖ ≤ |D q a n| + J q a 0 t β + J q a t n β := by
  dsimp only
  intro q a n t β _ ht
  let E (x : ℝ) := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let w (k : ℕ) : ℝ := if k % q = a % q then ArithmeticFunction.vonMangoldt k else 0
  let d (m : ℕ) : ℝ := (∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q=a % q),
    ArithmeticFunction.vonMangoldt k) - (m:ℝ)/(Nat.totient q:ℝ)
  let bReal (k : ℕ) : ℝ := w (k+1) - 1 / (Nat.totient q : ℝ)
  let b (k : ℕ) : ℂ := (bReal k : ℂ)
  let phase (k : ℕ) : ℂ := E (((k+1 : ℕ) : ℝ)*β)
  let B : ℝ := 2 * Real.pi * |β|
  have hB : 0 ≤ B := by unfold B; positivity
  have hunit (k : ℕ) : ‖phase k‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hstep (k : ℕ) : phase (k+1) = phase k * E β := by
    dsimp only [phase, E]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hdiff (k : ℕ) : ‖phase (k+1) - phase k‖ ≤ B := by
    rw [hstep, show phase k * E β - phase k = phase k * (E β - 1) by ring,
      norm_mul, hunit, one_mul]
    have hE : E β = Complex.exp (Complex.I * ((2*Real.pi*β : ℝ) : ℂ)) := by
      dsimp [E]
      rw [mul_comm]
    rw [hE]
    simpa [B, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*β))
  have hPrefixReal (m : ℕ) : (∑ k ∈ Finset.range m, bReal k) = d m := by
    have hzero : w 0 = 0 := by simp [w]
    have hshift := Finset.sum_range_succ' w m
    simp only [hzero, add_zero, zero_add] at hshift
    dsimp only [bReal]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hshift]
    simp only [d, Finset.sum_filter, w]
    ring
  have hPrefix (m : ℕ) : ‖∑ k ∈ Finset.range m, b k‖ = |d m| := by
    change ‖∑ k ∈ Finset.range m, (bReal k : ℂ)‖ = _
    rw [← Complex.ofReal_sum, hPrefixReal, Complex.norm_real, Real.norm_eq_abs]
  have hMain : ‖phase (n-1) • ∑ k ∈ Finset.range n, b k‖ = |d n| := by
    rw [norm_smul, hunit, one_mul, hPrefix]
  have hTerms : (∑ j ∈ Finset.range (n-1), |d (j+1)|) ≤
      ∑ m ∈ Finset.range n, |d m| := by
    have hReindex : (∑ j ∈ Finset.range (n-1), |d (j+1)|) =
        ∑ m ∈ Finset.Ico 1 n, |d m| := by
      refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
      · intro j hj
        have := Finset.mem_range.mp hj
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · intro i _ j _ hij
        omega
      · intro j hj
        have := Finset.mem_Ico.mp hj
        exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro j _
        rfl
    rw [hReindex]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
    · intro m _ _
      exact abs_nonneg (d m)
  have hTail : ‖∑ j ∈ Finset.range (n-1),
      (phase (j+1) - phase j) • ∑ k ∈ Finset.range (j+1), b k‖ ≤
      B * (∑ m ∈ Finset.range n, |d m|) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n-1),
          ‖(phase (j+1) - phase j) • ∑ k ∈ Finset.range (j+1), b k‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n-1), B * |d (j+1)| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, hPrefix]
        exact mul_le_mul_of_nonneg_right (hdiff j) (abs_nonneg _)
      _ = B * (∑ j ∈ Finset.range (n-1), |d (j+1)|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hTerms hB
  have hReindex : (∑ j ∈ Finset.range n, phase j • b j) =
      ∑ k ∈ Finset.Icc 1 n, ((w k - 1/(Nat.totient q:ℝ):ℝ):ℂ) * E ((k:ℝ)*β) := by
    refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i _ j _ hij
      omega
    · intro j hj
      have := Finset.mem_Icc.mp hj
      exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      simp only [phase, b, bReal, smul_eq_mul, mul_comm]
  change ‖∑ k ∈ Finset.Icc 1 n, ((w k - 1/(Nat.totient q:ℝ):ℝ):ℂ) * E ((k:ℝ)*β)‖ ≤
    |d n| + B * (∑ m ∈ Finset.Ico 0 t, |d m|) + B * (∑ m ∈ Finset.Ico t n, |d m|)
  rw [← hReindex, Finset.sum_range_by_parts]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ |d n| + B * (∑ m ∈ Finset.range n, |d m|) := add_le_add hMain.le hTail
    _ = _ := by
      rw [← Finset.range_eq_Ico, ← Finset.sum_range_add_sum_Ico _ ht]
      ring

open scoped BigOperators

private theorem earlyCost :
    let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); let T : ℕ := 8000000000; ∀ (q a n : ℕ) (β : ℝ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 4000000000000000000 ≤ n → |β| ≤ 105/(n:ℝ) → J q a 0 T β ≤ (n:ℝ)/10^12 := by

  dsimp only
  intro q a n β hq hqmax ha hcop hn hβ
  let T : ℕ := 8000000000
  let D : ℕ → ℝ := fun m => (∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (m:ℝ)/Nat.totient q
  change 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico 0 T, |D m|) ≤ (n:ℝ)/10^12
  have hT : (T:ℝ) ≤ (2:ℝ)^34 := by norm_num [T]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    linarith
  have hlog : Real.log (T:ℝ) ≤ 50 := by
    calc
      _ ≤ Real.log ((2:ℝ)^34) := Real.log_le_log (by norm_num [T]) hT
      _ = (34:ℝ)*Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 50 := by linarith
  have hΛ (k : ℕ) (hk : k ≤ T) : ArithmeticFunction.vonMangoldt k ≤ 50 := by
    by_cases hk0 : k = 0
    · subst k
      simp
    · exact ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by exact_mod_cast hk)).trans hlog)
  have htot : (1:ℝ) ≤ Nat.totient q := by
    exact_mod_cast (show 1 ≤ Nat.totient q from Nat.totient_pos.mpr (by omega))
  have hD (m : ℕ) (hm : m ∈ Finset.Ico 0 T) : |D m| ≤ 51*(T:ℝ) := by
    have hmt : m < T := (Finset.mem_Ico.mp hm).2
    let s := (Finset.range (m+1)).filter (fun k => k % q=a % q)
    have hs : s.card ≤ T := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using (show m+1 ≤ T by omega))
    have hsum0 : 0 ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k :=
      Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hsum : (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤ 50*(T:ℝ) := by
      calc
        _ ≤ ∑ k ∈ s, (50:ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkm := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          exact hΛ k (by omega)
        _ = (s.card:ℝ)*50 := by simp
        _ ≤ _ := by
          have hh : (s.card:ℝ) ≤ T := by exact_mod_cast hs
          linarith
    have hmR : (m:ℝ) ≤ T := by exact_mod_cast hmt.le
    have hdiv0 : 0 ≤ (m:ℝ)/Nat.totient q := by positivity
    have hdiv : (m:ℝ)/Nat.totient q ≤ (T:ℝ) := by
      apply (div_le_iff₀ (by linarith : (0:ℝ)<Nat.totient q)).mpr
      calc
        _ ≤ (T:ℝ) := hmR
        _ = (T:ℝ)*1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left htot (by positivity)
    change |(∑ k ∈ s, ArithmeticFunction.vonMangoldt k)-(m:ℝ)/Nat.totient q| ≤ _
    rw [abs_le]
    have hT0 : (0:ℝ) ≤ (T:ℝ) := by positivity
    constructor
    · linarith only [hsum0, hdiv, hT0]
    · calc
        _ ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k := sub_le_self _ hdiv0
        _ ≤ 50*(T:ℝ) := hsum
        _ ≤ 51*(T:ℝ) := mul_le_mul_of_nonneg_right (by norm_num) hT0
  have hS : (∑ m ∈ Finset.Ico 0 T, |D m|) ≤ 51*(T:ℝ)^2 := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico 0 T, 51*(T:ℝ) := Finset.sum_le_sum hD
      _ = _ := by simp [Nat.card_Ico]; ring
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast (show 1≤q by omega)
  have hden : (4000000000000000000:ℝ) ≤ (q:ℝ)*n := by
    calc
      _ ≤ (n:ℝ) := hnR
      _ = 1*(n:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hqR (by positivity)
  have hβ' : |β| ≤ (105:ℝ)/4000000000000000000 :=
    hβ.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hpi : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  calc
    _ ≤ 8*((105:ℝ)/4000000000000000000)*(51*(T:ℝ)^2) := by
      exact mul_le_mul (mul_le_mul hpi hβ' (abs_nonneg _) (by norm_num))
        hS (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
    _ ≤ (4000000000000000000:ℝ)/10^12 := by norm_num [T]
    _ ≤ _ := div_le_div_of_nonneg_right hnR (by norm_num)



private noncomputable def ph (M j k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / M) : ℝ) : ℂ) * Complex.I)

private theorem parseval_range (M : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.range M, ‖∑ k ∈ Finset.range M, f k * ph M j k‖ ^ 2)
      = (M : ℝ) * ∑ k ∈ Finset.range M, ‖f k‖ ^ 2 := by
  by_cases hM : M = 0
  · subst M
    simp
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hM
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have phase (j k : ℕ) : ph M j k = (ζ ^ k) ^ j := by
    unfold ph
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have unit (j k : ℕ) : ‖ph M j k‖ = 1 := by
    unfold ph
    exact Complex.norm_exp_ofReal_mul_I _
  have orth (k l : ℕ) (hk : k < M) (hl : l < M) :
      ∑ j ∈ Finset.range M, ph M j k * (starRingEnd ℂ) (ph M j l) =
        if k = l then (M : ℂ) else 0 := by
    have term (j : ℕ) : ph M j k * (starRingEnd ℂ) (ph M j l) = (ζ ^ k / ζ ^ l) ^ j := by
      rw [← Complex.inv_eq_conj (unit j l), phase, phase, div_pow, div_eq_mul_inv]
    simp_rw [term]
    by_cases hkl : k = l
    · subst l
      simp [div_self (pow_ne_zero k hζ0)]
    · rw [ite_eq_right hkl, geom_sum_eq]
      · have hpow (i : ℕ) : (ζ ^ i) ^ M = 1 := by
          rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        simp [div_pow, hpow]
      · exact fun h => hkl (hζ.pow_inj hk hl ((div_eq_one_iff_eq (pow_ne_zero _ hζ0)).mp h))
  have expand (j : ℕ) :
      (∑ k ∈ Finset.range M, f k * ph M j k) * (starRingEnd ℂ) (∑ k ∈ Finset.range M, f k * ph M j k) =
        ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M,
          f k * (starRingEnd ℂ) (f l) * (ph M j k * (starRingEnd ℂ) (ph M j l)) := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_mul]
    ring
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', expand]
  change (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M, _) = _
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  have inner (l : ℕ) (hl : l ∈ Finset.range M) :
      ∑ j ∈ Finset.range M, f k * (starRingEnd ℂ) (f l) * (ph M j k * (starRingEnd ℂ) (ph M j l)) =
        if k = l then (M : ℂ) * (f k * (starRingEnd ℂ) (f k)) else 0 := by
    rw [← Finset.mul_sum, orth k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)]
    split_ifs with h
    · rw [h, mul_comm]
    · exact mul_zero _
  rw [Finset.sum_congr rfl inner]
  simp [hk]


private theorem constantMode :
    ∀ a q : ℕ, 0 < q → Nat.Coprime a q → (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), Complex.exp (Complex.I*((2*Real.pi*(a:ℝ)*(r:ℝ)/(q:ℝ):ℝ):ℂ))) = (ArithmeticFunction.moebius q:ℂ) := by
  intro a q hq haq
  let E : ℕ → ℂ := fun r =>
    Complex.exp (Complex.I * ((2 * Real.pi * (a : ℝ) * (r : ℝ) / (q : ℝ) : ℝ) : ℂ))
  have hq0 : q ≠ 0 := hq.ne'
  have hind : ∀ r : ℕ, (if Nat.Coprime r q then (1 : ℂ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0 := by
    intro r
    have hg0 : Nat.gcd r q ≠ 0 := (Nat.gcd_pos_of_pos_right r hq).ne'
    have hdiv : (Nat.gcd r q).divisors = q.divisors.filter (fun d => d ∣ r) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff, hq0, hg0,
        ne_eq, not_false_eq_true, and_true]
      tauto
    have hmz : ((ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℤ) (Nat.gcd r q)) =
        (1 : ArithmeticFunction ℤ) (Nat.gcd r q) := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hmz
    have hmzC : (∑ d ∈ (Nat.gcd r q).divisors, (ArithmeticFunction.moebius d : ℂ)) =
        if Nat.gcd r q = 1 then (1 : ℂ) else 0 := by
      have hc := congrArg (Int.cast (R := ℂ)) hmz
      rw [Int.cast_sum] at hc
      rw [hc]
      split_ifs <;> simp
    rw [hdiv, Finset.sum_filter] at hmzC
    simpa only [Nat.coprime_iff_gcd_eq_one] using hmzC.symm
  have hswap : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E r =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r := by
    calc
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E r
        = ∑ r ∈ Finset.range q, (if Nat.Coprime r q then (1 : ℂ) else 0) * E r := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun r _ => ?_
          split_ifs <;> simp [E]
      _ = ∑ r ∈ Finset.range q,
            (∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0) * E r := by
          refine Finset.sum_congr rfl fun r _ => by rw [hind r]
      _ = ∑ r ∈ Finset.range q, ∑ d ∈ q.divisors,
            (if d ∣ r then (ArithmeticFunction.moebius d : ℂ) * E r else 0) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs <;> simp
      _ = ∑ d ∈ q.divisors, ∑ r ∈ Finset.range q,
            (if d ∣ r then (ArithmeticFunction.moebius d : ℂ) * E r else 0) := Finset.sum_comm
      _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
            ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.mul_sum, Finset.sum_filter]
  have hinner : ∀ d ∈ q.divisors,
      (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r) = if d = q then (1 : ℂ) else 0 := by
    intro d hd
    have hd_dvd : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    let m : ℕ := q / d
    have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hq hd_dvd) hd_pos
    have hdm : d * m = q := Nat.mul_div_cancel' hd_dvd
    let z : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)
    have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
    have hbij : (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r) =
        ∑ k ∈ Finset.range m, z ^ k := by
      symm
      refine Finset.sum_bij (fun k _ => d * k) ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_range]
        rw [Finset.mem_range] at hk
        refine ⟨?_, dvd_mul_right d k⟩
        rw [← hdm]
        exact Nat.mul_lt_mul_of_pos_left hk hd_pos
      · intro k₁ _ k₂ _ hkeq
        exact Nat.eq_of_mul_eq_mul_left hd_pos hkeq
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        rcases hr with ⟨hrq, ⟨k, rfl⟩⟩
        refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
        rw [← hdm] at hrq
        exact Nat.lt_of_mul_lt_mul_left hrq
      · intro k _
        simp only [z, E, ← Complex.exp_nat_mul]
        apply congrArg Complex.exp
        have hqC : (q : ℂ) = (d : ℂ) * (m : ℂ) := by
          rw [← hdm, Nat.cast_mul]
        simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_natCast, Nat.cast_mul]
        rw [hqC]
        field_simp [hd0, hm0]
    rw [hbij]
    by_cases hdq : d = q
    · rw [ite_eq_left_iff.mpr fun h => False.elim (h hdq)]
      have hm1 : m = 1 := by
        dsimp [m]
        rw [hdq, Nat.div_self hq]
      rw [hm1, Finset.range_one, Finset.sum_singleton, pow_zero]
    · rw [ite_eq_right_iff.mpr fun h => False.elim (hdq h)]
      have hm_ne1 : m ≠ 1 := by
        intro hm1
        apply hdq
        have := hdm
        rw [hm1, mul_one] at this
        exact this
      have hz_ne1 : z ≠ 1 := by
        intro hz1
        have hz1' : Complex.exp (2 * ↑Real.pi * Complex.I * (a : ℂ) / (m : ℂ)) = 1 := by
          rw [← hz1]
          apply congrArg Complex.exp
          simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
            Complex.ofReal_natCast]
          ring
        have hma : m ∣ a :=
          (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := a) (N := m) hm_pos.ne').mp hz1'
        have hmq : m ∣ q := ⟨d, by rw [mul_comm, hdm]⟩
        have hmg : m ∣ Nat.gcd a q := Nat.dvd_gcd hma hmq
        rw [haq.gcd_eq_one] at hmg
        exact hm_ne1 (Nat.eq_one_of_dvd_one hmg)
      rw [geom_sum_eq hz_ne1 m]
      have hzm : z ^ m = 1 := by
        have hexp : z ^ m = Complex.exp ((a : ℕ) * (2 * ↑Real.pi * Complex.I)) := by
          dsimp [z]
          rw [← Complex.exp_nat_mul]
          apply congrArg Complex.exp
          simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
            Complex.ofReal_natCast]
          field_simp [hm0]
        rw [hexp, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
      rw [hzm, sub_self, zero_div]
  rw [hswap]
  have hq_mem : q ∈ q.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hq0⟩
  calc
    ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) * (if d = q then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun d hd => by rw [hinner d hd]
    _ = ∑ d ∈ q.divisors, if d = q then (ArithmeticFunction.moebius d : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
    _ = (ArithmeticFunction.moebius q : ℂ) := by
        rw [Finset.sum_ite_eq']
        simp [hq_mem]

private theorem nonunitMass :
    ∀ q n : ℕ, 1 ≤ q → 1 ≤ n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q), ArithmeticFunction.vonMangoldt k) ≤ (q.primeFactors.card:ℝ)*Real.log n := by
  intro q n hq hn
  let K := (Finset.range (n+1)).filter (fun k => ¬k.Coprime q)
  let T := K.filter IsPrimePow
  let E (p : ℕ) := (Finset.Icc 1 (Nat.log p n))
  have repr {k : ℕ} (hk : k ∈ T) :
      k.minFac ∈ q.primeFactors ∧ ∃ a ∈ E k.minFac, k.minFac^a = k := by
    obtain ⟨hkK,hpp⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkN,hbad⟩ := Finset.mem_filter.mp hkK
    obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff k).1 hpp
    rw [Nat.pow_minFac ha.ne',hp.minFac_eq]
    have hd : p ∣ q := by
      by_contra h
      exact hbad ((hp.coprime_iff_not_dvd.2 h).pow_left a)
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩,a,Finset.mem_Icc.mpr ⟨ha,?_⟩,rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by have := Finset.mem_range.mp hkN; omega)
  have fiber (p : ℕ) (hp : p ∈ q.primeFactors) :
      (∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k) ≤ Real.log n := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hsub : T.filter (fun k => k.minFac=p) ⊆ (E p).image (fun a => p^a) := by
      intro k hk
      obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
      have hrep := (repr hkT).2
      rw [hbase] at hrep
      exact Finset.mem_image.mpr hrep
    have hc : (T.filter (fun k => k.minFac=p)).card ≤ Nat.log p n := by
      have := (Finset.card_le_card hsub).trans Finset.card_image_le
      simpa [E,Nat.card_Icc] using this
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    calc
      _ = ∑ _k ∈ T.filter (fun k => k.minFac=p), Real.log (p:ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
        rw [ArithmeticFunction.vonMangoldt_apply,ite_eq_left (Finset.mem_filter.mp hkT).2,hbase]
      _ ≤ (Nat.log p n:ℝ)*Real.log p := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlog
      _ = Real.log ((p:ℝ)^(Nat.log p n)) := (Real.log_pow _ _).symm
      _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast pow_pos hpprime.pos _)
        (by exact_mod_cast Nat.pow_log_le_self p (by omega))
  change (∑ k ∈ K, ArithmeticFunction.vonMangoldt k) ≤ _
  calc
    _ = ∑ k ∈ T, ArithmeticFunction.vonMangoldt k := by
      symm
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun k hk hout =>
        ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (fun h => hout (Finset.mem_filter.mpr ⟨hk,h⟩)))
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k :=
      (Finset.sum_fiberwise_of_maps_to (fun k hk => (repr hk).1) _).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log n := Finset.sum_le_sum fiber
    _ = _ := by simp


private noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

private noncomputable def P (q a m : ℕ) : ℝ :=
  (∑ k ∈ (range (m+1)).filter (fun k => k % q = a % q), vonMangoldt k) -
    (m:ℝ)/Nat.totient q

private def BMOR : Prop := ∀ (q a m : ℕ), 3 ≤ q → q ≤ 105 → a < q →
  Nat.Coprime a q → 8000000000 ≤ m →
    |(∑ k ∈ (range (m+1)).filter (fun k => k % q = a % q), vonMangoldt k) -
      (m:ℝ)/Nat.totient q| ≤ (m:ℝ)/(840*Real.log (m:ℝ))

private theorem logT : 22 ≤ Real.log (8000000000:ℝ) := by
  rw [show (8000000000:ℝ) = 2^12*5^9 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]

private theorem logL : 34 ≤ Real.log (600000000000000:ℝ) := by
  rw [show (600000000000000:ℝ) = 2^15*3*5^14 by norm_num,
    Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow,Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9,Real.log_three_gt_d9,Real.log_five_gt_d9]

private theorem logN (n : ℕ) (hn : 4000000000000000000 ≤ n) :
    42 ≤ Real.log (n:ℝ) := by
  have h : Real.log (4000000000000000000:ℝ) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [show (4000000000000000000:ℝ) = 2^20*5^18 by norm_num,
    Real.log_mul (by norm_num) (by norm_num),Real.log_pow,Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]

private theorem prefixSum (n : ℕ) : (∑ m ∈ range n, (m:ℝ)) ≤ (n:ℝ)^2/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,Nat.cast_succ]
    nlinarith only [ih]

private theorem prefixBound (h : BMOR) (q a m : ℕ) (hq : 3 ≤ q) (hq' : q ≤ 105)
    (ha : a < q) (hc : Nat.Coprime a q) (hm : 8000000000 ≤ m)
    (t : ℝ) (ht : 0 < t) (htm : t ≤ Real.log (m:ℝ)) :
    |P q a m| ≤ (m:ℝ)/(840*t) := by
  apply (h q a m hq hq' ha hc hm).trans
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left htm (by norm_num))

private theorem piBound : Real.pi ≤ 22/7 := by
  linarith [Real.pi_lt_d4]

private theorem threeRanges (h : BMOR) (q a n : ℕ) (β : ℝ)
    (hq : 3 ≤ q) (hq' : q ≤ 105) (ha : a < q) (hc : Nat.Coprime a q)
    (hn : 4000000000000000000 ≤ n) (hβ : |β| ≤ 105/(n:ℝ)) :
    ‖∑ k ∈ Icc 1 n, (((if k % q=a then vonMangoldt k else 0) -
      1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β)‖ ≤
      (n:ℝ)*(1/(10^9:ℝ)+1/(840*42)) +
        Real.pi*|β|*(n:ℝ)^2/(840*34) := by
  let T : ℕ := 8000000000
  let L : ℕ := 600000000000000
  let B := 2*Real.pi*|β|
  have hB : 0 ≤ B := by positivity
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hβ' : |β| ≤ (105:ℝ)/4000000000000000000 :=
    hβ.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hA := abelTwo q a n T β (by omega) (by dsimp [T]; omega)
  dsimp only at hA
  change ‖∑ k ∈ Icc 1 n, (((if k % q=a % q then vonMangoldt k else 0) -
      1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β)‖ ≤
      |P q a n| + B*(∑ m ∈ Ico 0 T, |P q a m|) +
        B*(∑ m ∈ Ico T n, |P q a m|) at hA
  have hmod : a % q = a := Nat.mod_eq_of_lt ha
  simp only [hmod] at hA
  have hEarly := earlyCost q a n β hq hq' ha hc hn hβ
  change B*(∑ m ∈ Ico 0 T, |P q a m|) ≤ (n:ℝ)/10^12 at hEarly
  have hEnd : |P q a n| ≤ (n:ℝ)/(840*42) :=
    prefixBound h q a n hq hq' ha hc (by omega) 42 (by norm_num) (logN n hn)
  have hmid : (∑ m ∈ Ico T L, |P q a m|) ≤ (L:ℝ)^2/(840*22) := by
    calc
      _ ≤ ∑ m ∈ Ico T L, (L:ℝ)/(840*22) := by
        apply sum_le_sum
        intro m hm
        have hmt := (mem_Ico.mp hm).1
        have hml := (mem_Ico.mp hm).2
        have hlog : 22 ≤ Real.log (m:ℝ) := logT.trans
          (Real.log_le_log (by norm_num) (by exact_mod_cast hmt))
        exact (prefixBound h q a m hq hq' ha hc hmt 22 (by norm_num) hlog).trans
          (div_le_div_of_nonneg_right (by exact_mod_cast hml.le) (by norm_num))
      _ = ((L-T:ℕ):ℝ)*((L:ℝ)/(840*22)) := by simp [Nat.card_Ico]
      _ ≤ _ := by
        have hlt : ((L-T:ℕ):ℝ) ≤ L := by exact_mod_cast Nat.sub_le L T
        calc
          _ ≤ (L:ℝ)*((L:ℝ)/(840*22)) := mul_le_mul_of_nonneg_right hlt (by positivity)
          _ = _ := by ring
  have hMidCost : B*(∑ m ∈ Ico T L, |P q a m|) ≤
      (n:ℝ)*(1/10^9-1/10^12) := by
    have hb : B ≤ 7*((105:ℝ)/4000000000000000000) := by
      dsimp only [B]
      exact mul_le_mul (by linarith [piBound] : 2*Real.pi ≤ 7) hβ'
        (abs_nonneg _) (by norm_num)
    calc
      _ ≤ 7*((105:ℝ)/4000000000000000000)*((L:ℝ)^2/(840*22)) :=
        mul_le_mul hb hmid (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
      _ ≤ (4000000000000000000:ℝ)*(1/10^9-1/10^12) := by norm_num [L]
      _ ≤ _ := mul_le_mul_of_nonneg_right hnR (by norm_num)
  have htail : (∑ m ∈ Ico L n, |P q a m|) ≤ (n:ℝ)^2/(2*(840*34)) := by
    calc
      _ ≤ ∑ m ∈ Ico L n, (m:ℝ)/(840*34) := by
        apply sum_le_sum
        intro m hm
        have hmL := (mem_Ico.mp hm).1
        have hlog : 34 ≤ Real.log (m:ℝ) := logL.trans
          (Real.log_le_log (by norm_num) (by exact_mod_cast hmL))
        exact prefixBound h q a m hq hq' ha hc (by dsimp [L] at hmL; omega) 34 (by norm_num) hlog
      _ = (∑ m ∈ Ico L n, (m:ℝ))/(840*34) := by rw [sum_div]
      _ ≤ _ := by
        have hs : (∑ m ∈ Ico L n, (m:ℝ)) ≤ (n:ℝ)^2/2 :=
          (sum_le_sum_of_subset_of_nonneg (t := range n)
            (fun m hm => mem_range.mpr (mem_Ico.mp hm).2) (by intros; positivity)).trans (prefixSum n)
        calc
          _ ≤ ((n:ℝ)^2/2)/(840*34) := div_le_div_of_nonneg_right hs (by norm_num)
          _ = _ := by ring
  have hTailCost : B*(∑ m ∈ Ico L n, |P q a m|) ≤
      Real.pi*|β|*(n:ℝ)^2/(840*34) := by
    calc
      _ ≤ B*((n:ℝ)^2/(2*(840*34))) := mul_le_mul_of_nonneg_left htail hB
      _ = _ := by dsimp [B]; ring
  have hs : (∑ m ∈ Ico T L, |P q a m|) + (∑ m ∈ Ico L n, |P q a m|) =
      ∑ m ∈ Ico T n, |P q a m| :=
    sum_Ico_consecutive _ (by norm_num [T,L]) (by dsimp [L]; omega)
  rw [← hs, mul_add] at hA
  linarith only [hA,hEarly,hEnd,hMidCost,hTailCost]
