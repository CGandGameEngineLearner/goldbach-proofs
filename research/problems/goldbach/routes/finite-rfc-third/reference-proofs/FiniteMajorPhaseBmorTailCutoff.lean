/- Reference proof for the proposed conditional cutoff.
   The three-range Abel estimate is adapted from FR-9011 (Apache-2.0). -/
import Mathlib

namespace BMORPhaseCutoff
open Finset

noncomputable def discrepancy (q a m : ℕ) : ℝ :=
  (∑ k ∈ (range (m+1)).filter (fun k => k % q = a % q),
    ArithmeticFunction.vonMangoldt k) - (m : ℝ) / q.totient

/-- A uniform elementary bound, including all prime powers. -/
theorem discrepancy_le_three (q a m : ℕ) (hq : 0 < q) :
    |discrepancy q a m| ≤ 3 * (m : ℝ) := by
  let s := (range (m+1)).filter (fun k => k % q = a % q)
  have hzero : 0 ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k :=
    sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hsum : (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤ Chebyshev.psi m := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have hkm := mem_range.mp (mem_filter.mp hk).1
      exact mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
    · intro k _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hmain : (m : ℝ) / q.totient ≤ m := by
    have ht : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    simpa using div_le_div_of_nonneg_left (Nat.cast_nonneg m)
      (by norm_num : (0:ℝ) < 1) ht
  have hpsi : Chebyshev.psi m ≤ 3 * (m : ℝ) := by
    by_cases hm : m = 0
    · simp [hm]
    have hx : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    let y := Real.sqrt (m : ℝ)
    have hy : 0 < y := Real.sqrt_pos.2 (by linarith)
    have hy2 : y^2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    have h8 : Real.log (8/3 : ℝ) ≤ 1 :=
      (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith [Real.exp_one_gt_d9])
    have ht := Real.log_le_sub_one_of_pos (div_pos hy (by norm_num : (0:ℝ) < 8/3))
    rw [Real.log_div hy.ne' (by norm_num)] at ht
    have hlog : Real.log (m : ℝ) ≤ (3/4) * y := by
      rw [← hy2, Real.log_pow]
      norm_num
      linarith
    have h4 : Real.log (4 : ℝ) ≤ 3/2 := by
      rw [show (4 : ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_lt_d9]
    have hC := Chebyshev.psi_le hx
    change Chebyshev.psi m ≤ Real.log 4 * (m : ℝ) + 2 * y * Real.log m at hC
    have hA := mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg m)
    have hB := mul_le_mul_of_nonneg_left hlog hy.le
    nlinarith only [hC, hA, hB, hy2]
  change |(∑ k ∈ s, ArithmeticFunction.vonMangoldt k) - (m:ℝ)/q.totient| ≤ _
  rw [abs_le]
  constructor
  · nlinarith only [hzero, hmain, Nat.cast_nonneg (α := ℝ) m]
  · linarith [hsum.trans hpsi, div_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m)
      (Nat.cast_nonneg q.totient)]

private theorem range_sum_le_half_square (N : ℕ) :
    (∑ k ∈ range N, (k : ℝ)) ≤ (N : ℝ)^2/2 := by
  by_cases hN : N=0
  · simp [hN]
  have h := congrArg (fun x : ℕ => (x : ℝ)) (Finset.sum_range_id_mul_two N)
  push_cast [Nat.cast_sub (by omega : 1 ≤ N)] at h
  nlinarith only [h,Nat.cast_nonneg (α := ℝ) N]

private theorem sum_class_le {s : Finset ℕ} {N : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hsub : s ⊆ range N) :
    (∑ k ∈ s, C * (k : ℝ)) ≤ C * (N : ℝ)^2 / 2 := by
  rw [← mul_sum, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hC
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
    (range_sum_le_half_square N)

def TailBound : Prop :=
  ∀ q a m : ℕ, 3 ≤ q → q ≤ 105 → a < q → a.Coprime q → 3000000000000 ≤ m →
    |discrepancy q a m| ≤ (m : ℝ) / (840 * Real.log m)

private theorem log22 {m : ℕ} (hm : 3000000000000 ≤ m) : 22 ≤ Real.log m := by
  apply (Real.le_log_iff_exp_le (by positivity : (0:ℝ) < m)).mpr
  calc
    Real.exp 22 = (Real.exp 1)^22 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (3 : ℝ)^22 := by gcongr; exact Real.exp_one_lt_three.le
    _ ≤ (3000000000000 : ℝ) := by norm_num
    _ ≤ m := by exact_mod_cast hm

/-- The small-index contribution to the Abel bound fits the existing
n/10^9 allowance even when the input starts at 3 * 10^12. -/
theorem early_middle_cost (h : TailBound) {q a n : ℕ} (hq : 3 ≤ q) (hq' : q ≤ 105)
    (ha : a < q) (hc : a.Coprime q) (hn : 4000000000000000000 ≤ n)
    {β : ℝ} (hβ : |β| ≤ 105/(n:ℝ)) :
    2 * Real.pi * |β| *
      (∑ k ∈ range 600000000000000, |discrepancy q a k|) ≤ (n:ℝ)/10^9 := by
  let U : ℕ := 3000000000000
  let V : ℕ := 600000000000000
  let E := (range V).filter (· < U)
  let M := (range V).filter (fun k => ¬ k < U)
  have hE : (∑ k ∈ E, |discrepancy q a k|) ≤ 3*(U:ℝ)^2/2 := by
    refine (sum_le_sum fun k _ => discrepancy_le_three q a k (by omega)).trans ?_
    exact sum_class_le (by norm_num) (fun k hk => mem_range.mpr (mem_filter.mp hk).2)
  have hM : (∑ k ∈ M, |discrepancy q a k|) ≤ (1/18480 : ℝ)*(V:ℝ)^2/2 := by
    refine (sum_le_sum (fun k hk => ?_)).trans
      (sum_class_le (by norm_num) (fun k hk => (mem_filter.mp hk).1))
    have hk' : U ≤ k := le_of_not_gt (mem_filter.mp hk).2
    have h22 := log22 hk'
    rw [one_div, inv_mul_eq_div]
    refine (h q a k hq hq' ha hc hk').trans ?_
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by norm_num) (by linarith)
  have hsum : (∑ k ∈ range V, |discrepancy q a k|) ≤ 24000000000000000000000000 := by
    rw [← sum_filter_add_sum_filter_not (p := fun k : ℕ => k < U)]
    have hd := add_le_add hE hM
    norm_num [U,V] at hd
    exact hd.trans (by norm_num)
  have hnR : (4000000000000000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hf : 2 * Real.pi * |β| ≤ (660:ℝ)/(n:ℝ) := by
    calc
      _ ≤ 2 * Real.pi * (105/(n:ℝ)) :=
        mul_le_mul_of_nonneg_left hβ (by positivity)
      _ ≤ _ := by
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hn0.le
        linarith [Real.pi_lt_d4]
  calc
    _ ≤ 2 * Real.pi * |β| * 24000000000000000000000000 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (660/(n:ℝ)) * 24000000000000000000000000 :=
      mul_le_mul_of_nonneg_right hf (by norm_num)
    _ ≤ _ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
      have hsq : (4000000000000000000 : ℝ)^2 ≤ (n:ℝ)^2 :=
        pow_le_pow_left₀ (by norm_num) hnR 2
      calc
        _ ≤ (4000000000000000000 : ℝ)^2 / 10^9 := by norm_num
        _ ≤ (n:ℝ)^2/10^9 := div_le_div_of_nonneg_right hsq (by positivity)
        _ = (n:ℝ)/10^9*(n:ℝ) := by ring

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private theorem Enorm (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  exact Complex.norm_exp_ofReal_mul_I _

private theorem Eadd (x y : ℝ) : E (x+y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem Estep (β : ℝ) (k : ℕ) :
    ‖E (((k+1 : ℕ):ℝ)*β) - E ((k:ℝ)*β)‖ ≤ 2*Real.pi*|β| := by
  rw [Nat.cast_succ, add_mul, one_mul, Eadd, ← mul_sub_one, norm_mul, Enorm, one_mul]
  unfold E
  rw [mul_comm _ Complex.I]
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ 2*Real.pi by positivity)] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*β))

private theorem log34 {m : ℕ} (hm : 600000000000000 ≤ m) : 34 ≤ Real.log m := by
  have hm' : 0 < m := by omega
  have hmR : (0:ℝ) < m := by exact_mod_cast hm'
  apply (Real.le_log_iff_exp_le hmR).mpr
  calc
    Real.exp 34 = (Real.exp 1)^34 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (2719/1000:ℝ)^34 := by gcongr; linarith [Real.exp_one_lt_d9]
    _ ≤ (600000000000000:ℝ) := by norm_num
    _ ≤ m := by exact_mod_cast hm

private theorem log42 {m : ℕ} (hm : 4000000000000000000 ≤ m) : 42 ≤ Real.log m := by
  have hm' : 0 < m := by omega
  have hmR : (0:ℝ) < m := by exact_mod_cast hm'
  apply (Real.le_log_iff_exp_le hmR).mpr
  calc
    Real.exp 42 = (Real.exp 1)^42 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (2719/1000:ℝ)^42 := by gcongr; linarith [Real.exp_one_lt_d9]
    _ ≤ (4000000000000000000:ℝ) := by norm_num
    _ ≤ m := by exact_mod_cast hm

/-- Same conclusion as FiniteMajorPhaseBmorThreeRanges, with the required
progression estimate beginning at 3 * 10^12 instead of 8 * 10^9. -/
theorem phase_of_tail (h : TailBound) {q a n : ℕ} (hq : 3 ≤ q) (hq' : q ≤ 105)
    (ha : a < q) (hc : a.Coprime q) (hn : 4000000000000000000 ≤ n)
    {β : ℝ} (hβ : |β| ≤ 105/(n:ℝ)) :
    ‖∑ k ∈ Icc 1 n,
        (((if k%q=a then ArithmeticFunction.vonMangoldt k else 0) -
          1/(q.totient:ℝ) : ℝ) : ℂ) * E ((k:ℝ)*β)‖ ≤
      (n:ℝ)*(1/(10^9:ℝ)+1/(840*42)) + Real.pi * |β| * (n:ℝ)^2/(840*34) := by
  let f (k : ℕ) : ℝ := if k%q=a then ArithmeticFunction.vonMangoldt k else 0
  let b (k : ℕ) : ℂ := ((f k - (if k=0 then 0 else 1/(q.totient:ℝ)) : ℝ) : ℂ)
  let z (k : ℕ) : ℂ := E ((k:ℝ)*β)
  have hb0 : b 0 = 0 := by simp [b,f]
  have hzn : ∀ k, ‖z k‖ = 1 := fun k => Enorm _
  have hsum (k : ℕ) : (∑ j ∈ range (k+1), b j) = (discrepancy q a k : ℂ) := by
    rw [discrepancy, sum_filter]
    change (∑ j ∈ range (k+1), ((f j - (if j=0 then 0 else 1/(q.totient:ℝ)) : ℝ) : ℂ)) = _
    rw [← Complex.ofReal_sum, sum_sub_distrib]
    congr 2
    · apply sum_congr rfl
      intro j _
      simp [f, Nat.mod_eq_of_lt ha]
    · rw [sum_range_succ']
      simp [nsmul_eq_mul, div_eq_mul_inv]
  have hIcc : Icc 1 n = (range (n+1)).filter (· ≠ 0) := by
    ext k
    simp only [mem_Icc, mem_range, mem_filter]
    omega
  have heq :
      (∑ k ∈ Icc 1 n, (((if k%q=a then ArithmeticFunction.vonMangoldt k else 0) -
          1/(q.totient:ℝ) : ℝ) : ℂ)*z k) =
        ∑ k ∈ range (n+1), b k * z k := by
    rw [hIcc, sum_filter]
    apply sum_congr rfl
    intro k _
    by_cases hk : k=0
    · simp [hk,hb0]
    · simp [b,f,hk]
  have hab :
      (∑ k ∈ range (n+1), b k * z k) =
        (∑ k ∈ range (n+1), b k) * z n -
          ∑ k ∈ range n, (∑ j ∈ range (k+1), b j) * (z (k+1)-z k) := by
    simpa only [smul_eq_mul, Nat.add_sub_cancel] using
      (Finset.sum_range_by_parts' (f := b) (g := z) (n := n+1))
  have hn' : 3000000000000 ≤ n := by omega
  have hlast : |discrepancy q a n| ≤ (n:ℝ)/(840*42) :=
    (h q a n hq hq' ha hc hn').trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith [log42 hn]))
  let late := (range n).filter (fun k => ¬ k < 600000000000000)
  let early := (range n).filter (· < 600000000000000)
  have hl : (∑ k ∈ late, |discrepancy q a k|) ≤ (1/28560:ℝ)*(n:ℝ)^2/2 := by
    refine (sum_le_sum (fun k hk => ?_)).trans
      (sum_class_le (by norm_num) (filter_subset _ _))
    have hcut : 600000000000000 ≤ k := le_of_not_gt (mem_filter.mp hk).2
    rw [one_div, inv_mul_eq_div]
    exact (h q a k hq hq' ha hc (by omega)).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith [log34 hcut]))
  have he : early = range 600000000000000 := by
    ext k
    simp only [early, mem_filter, mem_range]
    omega
  change ‖∑ k ∈ Icc 1 n, _ * z k‖ ≤ _
  rw [heq, hab, hsum n]
  have hb (k : ℕ) :
      ‖(∑ j ∈ range (k+1), b j) * (z (k+1)-z k)‖ ≤
        (2 * Real.pi * |β|) * |discrepancy q a k| := by
    rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (Estep β k) (abs_nonneg _)
  have hrem :
      ‖∑ k ∈ range n, (∑ j ∈ range (k+1), b j)*(z (k+1)-z k)‖ ≤
        (n:ℝ)/10^9 + Real.pi * |β| * (n:ℝ)^2/(840*34) := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun k _ => hb k).trans ?_)
    rw [← mul_sum, ← sum_filter_add_sum_filter_not (p := fun k : ℕ => k < 600000000000000)]
    change (2 * Real.pi * |β|) *
      ((∑ k ∈ early, |discrepancy q a k|)+(∑ k ∈ late, |discrepancy q a k|)) ≤ _
    rw [mul_add, he]
    convert add_le_add (early_middle_cost h hq hq' ha hc hn hβ)
      (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2*Real.pi*|β|)) using 1
    ring
  have hf : ‖(discrepancy q a n : ℂ) * z n‖ ≤ (n:ℝ)/(840*42) := by
    rw [norm_mul, hzn, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hlast
  have result := (norm_sub_le _ _).trans (add_le_add hf hrem)
  linarith only [result]

end BMORPhaseCutoff

#print axioms BMORPhaseCutoff.early_middle_cost
#print axioms BMORPhaseCutoff.phase_of_tail

set_option autoImplicit false in
theorem Conjectures.Goldbach.FiniteMajorPhaseBmorTailCutoff :
    (∀ (q a m : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 3000000000000 ≤ m → |(∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (m:ℝ)/Nat.totient q| ≤ (m:ℝ)/(840*Real.log (m:ℝ))) → let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (q a n : ℕ) (β : ℝ), 3≤q → q≤105 → a<q → Nat.Coprime a q → 4000000000000000000≤n → |β|≤105/(n:ℝ) → ‖∑ k ∈ Finset.Icc 1 n, (((if k%q=a then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β)‖ ≤ (n:ℝ)*(1/(10^9:ℝ)+1/(840*42)) + Real.pi * |β| * (n:ℝ)^2/(840*34) := by
  intro h
  dsimp only
  intro q a n β hq hQ ha hc hn hβ
  exact BMORPhaseCutoff.phase_of_tail h hq hQ ha hc hn hβ

#print axioms Conjectures.Goldbach.FiniteMajorPhaseBmorTailCutoff
