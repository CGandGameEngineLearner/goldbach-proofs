import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) = if n = 1 then 1 else 0 := by
  have h : ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) * ArithmeticFunction.zeta) n
      = (1 : ArithmeticFunction ℂ) n := by
    rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simpa using h

lemma sum_coprime_eq_sum_moebius (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ) :
    ∑ b ∈ (Finset.range N).filter (fun b => Nat.Coprime b N), f b
      = ∑ d ∈ N.divisors,
          (ArithmeticFunction.moebius d : ℂ) * ∑ j ∈ Finset.range (N / d), f (d * j) := by
  have hstep1 : ∀ d ∈ N.divisors,
      ∑ j ∈ Finset.range (N / d), f (d * j)
        = ∑ m ∈ (Finset.range N).filter (fun m => d ∣ m), f m := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hN
    have hNd : d * (N / d) = N := by
      rw [mul_comm]
      exact Nat.div_mul_cancel hdvd
    have hset : (Finset.range N).filter (fun m => d ∣ m)
        = (Finset.range (N / d)).image (fun j => d * j) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hmN, j, hjm⟩
        refine ⟨j, ?_, hjm.symm⟩
        rw [hjm] at hmN
        rw [← hNd] at hmN
        exact lt_of_mul_lt_mul_left hmN (Nat.zero_le d)
      · rintro ⟨j, hj, hjm⟩
        have hmN : m < N := by
          rw [← hjm, ← hNd]
          exact mul_lt_mul_of_pos_left hj hdpos
        exact ⟨hmN, j, hjm.symm⟩
    rw [hset, Finset.sum_image]
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hdpos hxy
  have hR1 : ∑ d ∈ N.divisors,
        (ArithmeticFunction.moebius d : ℂ) * ∑ j ∈ Finset.range (N / d), f (d * j)
      = ∑ d ∈ N.divisors,
          (ArithmeticFunction.moebius d : ℂ)
            * ∑ m ∈ (Finset.range N).filter (fun m => d ∣ m), f m := by
    exact Finset.sum_congr rfl fun d hd => by rw [hstep1 d hd]
  have hR2 : (∑ d ∈ N.divisors,
          (ArithmeticFunction.moebius d : ℂ)
            * ∑ m ∈ (Finset.range N).filter (fun m => d ∣ m), f m)
      = ∑ m ∈ Finset.range N,
          ∑ d ∈ N.divisors.filter (fun d => d ∣ m), (ArithmeticFunction.moebius d : ℂ) * f m := by
    simp only [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d ∣ m <;> simp [h]
  have hR3 : (∑ m ∈ Finset.range N,
          ∑ d ∈ N.divisors.filter (fun d => d ∣ m), (ArithmeticFunction.moebius d : ℂ) * f m)
      = ∑ m ∈ Finset.range N, (if Nat.Coprime m N then 1 else 0) * f m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    have hfilter : N.divisors.filter (fun d => d ∣ m) = (Nat.gcd m N).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdN, -⟩, hdm⟩
        exact ⟨Nat.dvd_gcd hdm hdN, (Nat.gcd_pos_of_pos_right m hN).ne'⟩
      · rintro ⟨hdg, -⟩
        obtain ⟨hdm, hdN⟩ := (Nat.dvd_gcd_iff).mp hdg
        exact ⟨⟨hdN, hN.ne'⟩, hdm⟩
    rw [hfilter, sum_moebius_divisors]
  have hR4 : (∑ m ∈ Finset.range N, (if Nat.Coprime m N then 1 else 0) * f m)
      = ∑ b ∈ (Finset.range N).filter (fun b => Nat.Coprime b N), f b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : Nat.Coprime m N <;> simp [h]
  rw [← hR4, ← hR3, ← hR2, ← hR1]

lemma ramanujan_sum_gen (N : ℕ) (hN : 0 < N) (w : ℂ) (hw : IsPrimitiveRoot w N)
    (a : ℕ) (ha : Nat.Coprime a N) :
    ∑ b ∈ (Finset.range N).filter (fun b => Nat.Coprime b N), w ^ (a * b)
      = (ArithmeticFunction.moebius N : ℂ) := by
  rw [sum_coprime_eq_sum_moebius N hN (fun b => w ^ (a * b))]
  have hinner : ∀ d ∈ N.divisors, d ≠ N →
      (ArithmeticFunction.moebius d : ℂ) * ∑ j ∈ Finset.range (N / d), w ^ (a * (d * j)) = 0 := by
    intro d hd hdne
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have hNd : d * (N / d) = N := by
      rw [mul_comm]
      exact Nat.div_mul_cancel hdvd
    have hpow : (w ^ (a * d)) ^ (N / d) = 1 := by
      rw [← pow_mul]
      have hmul : a * d * (N / d) = a * N := by rw [mul_assoc, hNd]
      rw [hmul, mul_comm a N, pow_mul, hw.pow_eq_one, one_pow]
    have hne : w ^ (a * d) ≠ 1 := by
      intro h1
      have hNdvd : N ∣ a * d := (hw.pow_eq_one_iff_dvd (a * d)).mp h1
      have hNd' : N ∣ d := (ha.symm.dvd_mul_left).mp hNdvd
      exact hdne (Nat.dvd_antisymm hdvd hNd')
    have hzero : ∑ j ∈ Finset.range (N / d), (w ^ (a * d)) ^ j = 0 := by
      have hgm : (∑ j ∈ Finset.range (N / d), (w ^ (a * d)) ^ j) * (w ^ (a * d) - 1) = 0 := by
        rw [geom_sum_mul, hpow, sub_self]
      rcases mul_eq_zero.mp hgm with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    have hsub : ∑ j ∈ Finset.range (N / d), w ^ (a * (d * j))
        = ∑ j ∈ Finset.range (N / d), (w ^ (a * d)) ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_mul]
      congr 1
      ring
    rw [hsub, hzero, mul_zero]
  have hmain : (∑ d ∈ N.divisors,
        (ArithmeticFunction.moebius d : ℂ) * ∑ j ∈ Finset.range (N / d), w ^ (a * (d * j)) : ℂ)
      = (ArithmeticFunction.moebius N : ℂ) := by
    rw [Finset.sum_eq_single N hinner (by
      intro hnot
      exact absurd (Nat.mem_divisors.mpr ⟨dvd_rfl, hN.ne'⟩) hnot)]
    rw [Nat.div_self hN, Finset.sum_range_one]
    simp
  exact hmain

lemma ramanujan_sum_exp (N : ℕ) (hN : 0 < N) (a : ℕ) (ha : Nat.Coprime a N) :
    ∑ b ∈ (Finset.range N).filter (fun b => Nat.Coprime b N),
        Complex.exp (((2 * Real.pi * (a:ℝ) * (b:ℝ) / (N:ℝ) : ℝ) : ℂ) * Complex.I)
      = (ArithmeticFunction.moebius N : ℂ) := by
  have harg : ((2 * Real.pi / (N:ℝ) : ℝ) : ℂ) * Complex.I
      = 2 * (Real.pi : ℂ) * Complex.I / (N : ℂ) := by
    push_cast
    field_simp
  have hw : IsPrimitiveRoot (Complex.exp (((2 * Real.pi / (N:ℝ) : ℝ) : ℂ) * Complex.I)) N := by
    rw [harg]
    exact Complex.isPrimitiveRoot_exp N hN.ne'
  rw [← ramanujan_sum_gen N hN _ hw a ha]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp


/-- The Ramanujan sum modulo 154 at any coprime frequency equals the Möbius value. -/
theorem L_goldbach_cert_154 :
    ∀ a:ℕ, Nat.Coprime a 154 → (∑ b ∈ (Finset.range 154).filter (fun b => Nat.Coprime b 154), Complex.exp (((2*Real.pi*(a:ℝ)*b/154:ℝ):ℂ)*Complex.I))/(60:ℂ)=(-1:ℂ)/60 := by
  intro a ha
  have hm : (ArithmeticFunction.moebius 154 : ℤ) = -1 := by
    have h2 : ArithmeticFunction.moebius 2 = -1 :=
      ArithmeticFunction.moebius_apply_prime (by norm_num)
    have h7 : ArithmeticFunction.moebius 7 = -1 :=
      ArithmeticFunction.moebius_apply_prime (by norm_num)
    have h11 : ArithmeticFunction.moebius 11 = -1 :=
      ArithmeticFunction.moebius_apply_prime (by norm_num)
    have h77 : ArithmeticFunction.moebius 77
        = ArithmeticFunction.moebius 7 * ArithmeticFunction.moebius 11 := by
      rw [show (77:ℕ) = 7 * 11 by norm_num]
      exact ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius (by norm_num)
    have h154 : ArithmeticFunction.moebius 154
        = ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius 77 := by
      rw [show (154:ℕ) = 2 * 77 by norm_num]
      exact ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius (by norm_num)
    rw [h154, h2, h77, h7, h11]
    norm_num
  have hsum : (∑ b ∈ (Finset.range 154).filter (fun b => Nat.Coprime b 154),
        Complex.exp (((2 * Real.pi * (a:ℝ) * (b:ℝ) / (154:ℝ) : ℝ) : ℂ) * Complex.I))
      = (ArithmeticFunction.moebius 154 : ℂ) :=
    ramanujan_sum_exp 154 (by norm_num) a ha
  rw [hsum]
  rw [hm]
  norm_num

end PEqualNP.Outside
