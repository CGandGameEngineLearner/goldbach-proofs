import Mathlib

namespace Conjectures.Goldbach.MobiusComplementaryCutoffs_aux

lemma max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
  · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]

lemma sum_moebius_divisors_eq_zero {n : ℕ} (hn : n ≠ 1) :
    n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ)) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ))
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h
  rw [ArithmeticFunction.one_apply_ne hn] at h
  exact h

lemma moebius_mul_moebius_div {n d : ℕ} (hsq : Squarefree n) (hd : d ∣ n) :
    ArithmeticFunction.moebius n * ArithmeticFunction.moebius d
      = ArithmeticFunction.moebius (n / d) := by
  have hdn : n / d * d = n := Nat.div_mul_cancel hd
  have hcop : Nat.Coprime (n / d) d := by
    refine Nat.coprime_of_squarefree_mul ?_
    rw [hdn]
    exact hsq
  have hmul0 : ArithmeticFunction.moebius (n / d * d)
      = ArithmeticFunction.moebius (n / d) * ArithmeticFunction.moebius d :=
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hcop
  have hmul : ArithmeticFunction.moebius n
      = ArithmeticFunction.moebius (n / d) * ArithmeticFunction.moebius d := by
    rw [hdn] at hmul0
    exact hmul0
  have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hd hsq
  have hone : ArithmeticFunction.moebius d ^ 2 = 1 :=
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsq
  calc ArithmeticFunction.moebius n * ArithmeticFunction.moebius d
      = ArithmeticFunction.moebius (n / d) * (ArithmeticFunction.moebius d ^ 2) := by
        rw [hmul]
        ring
    _ = ArithmeticFunction.moebius (n / d) := by rw [hone, mul_one]

lemma log_sub_log_div {n d : ℕ} (hd : d ∣ n) (hn : n ≠ 0) :
    Real.log (n : ℝ) - Real.log (d : ℝ) = Real.log ((n / d : ℕ) : ℝ) := by
  have hd0 : d ≠ 0 := by
    have hdmem : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hd, hn⟩
    exact (Nat.pos_of_mem_divisors hdmem).ne'
  have h1 : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := Nat.cast_div hd (by exact_mod_cast hd0)
  rw [h1, Real.log_div (by exact_mod_cast hn) (by exact_mod_cast hd0)]

end Conjectures.Goldbach.MobiusComplementaryCutoffs_aux

open Conjectures.Goldbach.MobiusComplementaryCutoffs_aux

theorem Conjectures.Goldbach.MobiusComplementaryCutoffs :
    ∀ (n : ℕ) (t : ℝ), 1 < n → Squarefree n → let T := fun x : ℝ => n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) * max (x - Real.log (d : ℝ)) 0); ArithmeticFunction.vonMangoldt n = T t - (ArithmeticFunction.moebius n : ℝ) * T (Real.log (n : ℝ) - t) := by
  intro n t hn hsq
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  simp only []
  have hsecond : (ArithmeticFunction.moebius n : ℝ) *
        n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
          max (Real.log (n : ℝ) - t - Real.log (d : ℝ)) 0)
      = n.divisors.sum (fun d => (ArithmeticFunction.moebius (n / d) : ℝ) *
          max (Real.log ((n / d : ℕ) : ℝ) - t) 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hmu : (ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius d : ℝ)
        = (ArithmeticFunction.moebius (n / d) : ℝ) := by
      rw [← Int.cast_mul, moebius_mul_moebius_div hsq hdvd]
    have hlog : Real.log (n : ℝ) - t - Real.log (d : ℝ) = Real.log ((n / d : ℕ) : ℝ) - t := by
      have h2 := log_sub_log_div hdvd hn0
      linarith
    rw [← mul_assoc, hmu, hlog]
  have hthird : n.divisors.sum (fun d => (ArithmeticFunction.moebius (n / d) : ℝ) *
          max (Real.log ((n / d : ℕ) : ℝ) - t) 0)
      = n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
          max (Real.log (d : ℝ) - t) 0) :=
    Nat.sum_div_divisors n (fun d => (ArithmeticFunction.moebius d : ℝ) *
      max (Real.log (d : ℝ) - t) 0)
  have hfourth : n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
          max (t - Real.log (d : ℝ)) 0)
      - n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
          max (Real.log (d : ℝ) - t) 0)
      = n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
          (t - Real.log (d : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 : max (t - Real.log (d : ℝ)) 0 - max (Real.log (d : ℝ) - t) 0
        = t - Real.log (d : ℝ) := by
      have h2 : Real.log (d : ℝ) - t = -(t - Real.log (d : ℝ)) := by ring
      rw [h2, max_sub_max_neg]
    rw [← mul_sub, h1]
  have hfifth : n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
          (t - Real.log (d : ℝ)))
      = t * n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ))
        - n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) := by
    calc n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
          (t - Real.log (d : ℝ)))
        = n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) * t
            - (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d _
          ring
      _ = n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) * t)
          - n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
              Real.log (d : ℝ)) := by rw [Finset.sum_sub_distrib]
      _ = t * n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ))
          - n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
              Real.log (d : ℝ)) := by
          rw [← Finset.sum_mul]
          ring
  have hlogsum : n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) *
        Real.log (d : ℝ)) = -ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.sum_moebius_mul_log_eq
  have hzero : n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ)) = 0 :=
    sum_moebius_divisors_eq_zero hn1
  rw [hsecond, hthird, hfourth, hfifth, hlogsum, hzero]
  ring
