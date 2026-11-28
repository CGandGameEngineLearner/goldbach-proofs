import Mathlib
import Conjectures.Goldbach.RoughFifthMass

open Filter Finset OAI.LargePrimeGaps
open scoped Topology

-- child 1 zh: 在经典 BV 截止点与 X 的平方根之间，对所有素因子均不超过 X 的四次方根的模数，控制最坏既约类误差之和。
-- child 1 en: In every fixed logarithmic collar below the square root, bound the total worst-class error for moduli whose prime factors are all at most the fourth root of X.
-- child 2 zh: 在同一窄带写 q=d p，其中 p 为大于 X 四次方根的素数，d 不超过该四次方根；控制对这些乘积的最坏既约类误差之和。
-- child 2 en: Bound the collar sum after writing each remaining modulus as d times a prime exceeding the fourth root of X, with cofactor d at most the fourth root.

theorem Conjectures.Cuts.Cut07c284deae92aa99df4807b6
    (hSmooth : ∀ A b : ℝ, 0 < A → 0 < b → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X ≥ N,
      let E := fun q : ℕ => ((Finset.range q).sup fun a =>
        if a.Coprime q then (NNReal.mk (|(∑ k ∈ (Finset.Ioc 0 X).filter (fun k => k % q = a), ArithmeticFunction.vonMangoldt k) -
          (X:ℝ)/q.totient|) (abs_nonneg _)) else 0)
      let hi := ⌊(X:ℝ)^(1/2:ℝ)⌋₊
      let lo := ⌊(X:ℝ)^(1/2:ℝ)/(Real.log X)^b⌋₊
      (∑ q ∈ (Finset.Ioc lo hi).filter (fun q => ∀ p ∈ q.primeFactors, p^4 ≤ X), (E q : ℝ))
        ≤ C*(X:ℝ)/(Real.log X)^A)
    (hSwitched : ∀ A b : ℝ, 0 < A → 0 < b → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X ≥ N,
      let E := fun q : ℕ => ((Finset.range q).sup fun a =>
        if a.Coprime q then (NNReal.mk (|(∑ k ∈ (Finset.Ioc 0 X).filter (fun k => k % q = a), ArithmeticFunction.vonMangoldt k) -
          (X:ℝ)/q.totient|) (abs_nonneg _)) else 0)
      let hi := ⌊(X:ℝ)^(1/2:ℝ)⌋₊
      let lo := ⌊(X:ℝ)^(1/2:ℝ)/(Real.log X)^b⌋₊
      (∑ z ∈ ((Finset.Icc 1 hi).product (Finset.Icc 1 hi)).filter (fun z =>
        z.2.Prime ∧ X < z.2^4 ∧ z.1^4 ≤ X ∧ lo < z.1*z.2 ∧ z.1*z.2 ≤ hi), (E (z.1*z.2) : ℝ))
        ≤ C*(X:ℝ)/(Real.log X)^A) : (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℝ) (x4 : ℕ), (0 : ℝ) < x3 ∧ ∀ (x5 : ℕ), x4 ≤ x5 → ∃ (x7 : ℕ → ℝ), (∀ x8 ∈ Finset.Icc (1 : ℕ) ⌊(↑x5 : ℝ) ^ (1 / 2 : ℝ)⌋₊, ∀ (x10 : ℕ), x10.Coprime x8 → |∑ x12 ∈ Finset.Icc (1 : ℕ) x5 with x12 % x8 = x10 % x8, (ArithmeticFunction.vonMangoldt : ℕ → ℝ) x12 - (↑x5 : ℝ) / (↑x8.totient : ℝ)| ≤ x7 x8) ∧ ∑ x8 ∈ Finset.Icc (1 : ℕ) ⌊(↑x5 : ℝ) ^ (1 / 2 : ℝ)⌋₊, x7 x8 ≤ x3 * (↑x5 : ℝ) / Real.log (↑x5 : ℝ) ^ x1) := by
  classical



  let err (X q : ℕ) : ℝ := (endpointError X q : ℝ)

  have majorize (X q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
      |(∑ k ∈ (Icc 1 X).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k)
         - (X : ℝ) / q.totient| ≤ err X q := by
    have hc : (a % q).Coprime q := by simpa [Nat.Coprime] using ha
    have h := endpointClassError_le X (Nat.mod_lt a hq) hc
    have heq : Ioc 0 X = Icc 1 X := by
      ext k
      simp only [mem_Ioc,mem_Icc]
      omega
    simpa only [err, residuePrefix, residueSlice, heq] using h

  have classical_range (A : ℝ) (hA : 0 < A) :
      ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∃ N : ℕ, ∀ X ≥ N,
        (∑ q ∈ Icc 1 ⌊(X:ℝ)^(1/2:ℝ) / (Real.log X)^b⌋₊, err X q)
          ≤ C*(X:ℝ)/(Real.log X)^A := by
    obtain ⟨b,hb,C,hC,x₀,hx₀,h⟩ := roughFifthBV A hA
    refine ⟨b,C,hb,hC, ⌈x₀⌉₊, ?_⟩
    intro X hX
    have hx : x₀ ≤ (X : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hX)
    have hlog : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by linarith)
    simpa only [err, Real.rpow_neg hlog, div_eq_mul_inv] using h (X:ℝ) hx

  have join_bands (X low high : ℕ) :
      ∑ q ∈ Icc 1 high, err X q ≤
      (∑ q ∈ Icc 1 low, err X q) + ∑ q ∈ Ioc low high, err X q := by
    by_cases h : low ≤ high
    · have hd : Disjoint (Icc 1 low) (Ioc low high) := by
        rw [Finset.disjoint_left]
        intro q h₁ h₂
        exact (not_lt_of_ge (mem_Icc.mp h₁).2) (mem_Ioc.mp h₂).1
      have heq : Icc 1 high = (Icc 1 low) ∪ (Ioc low high) := by
        ext q
        simp only [mem_Icc,mem_union,mem_Ioc]
        omega
      rw [heq, sum_union hd]
    · have sub : Icc 1 high ⊆ Icc 1 low := Icc_subset_Icc_right (by omega)
      exact (sum_le_sum_of_subset_of_nonneg sub (fun q _ _ => (endpointError X q).coe_nonneg)).trans
        (le_add_of_nonneg_right (sum_nonneg fun q _ => (endpointError X q).coe_nonneg))


  let smooth (X q : ℕ) : Prop := ∀ p ∈ q.primeFactors, p^4 ≤ X

  let factorPairs (X lo hi : ℕ) : Finset (ℕ × ℕ) :=
    ((Icc 1 hi).product (Icc 1 hi)).filter (fun z =>
      z.2.Prime ∧ X < z.2^4 ∧ z.1^4 ≤ X ∧ lo < z.1*z.2 ∧ z.1*z.2 ≤ hi)

  have switched (X lo : ℕ) :
      let hi := ⌊(X:ℝ)^(1/2:ℝ)⌋₊
      ∑ q ∈ (Ioc lo hi).filter (fun q => ¬ smooth X q), err X q ≤
        ∑ z ∈ factorPairs X lo hi, err X (z.1*z.2) := by
    classical
    intro hi
    let bad := (Ioc lo hi).filter (fun q => ¬ smooth X q)
    let pairs := factorPairs X lo hi
    let prod := fun z : ℕ × ℕ => z.1*z.2
    have cover : bad ⊆ pairs.image prod := by
      intro q hq
      obtain ⟨hqI,hs⟩ := mem_filter.mp hq
      obtain ⟨hl,hhi⟩ := mem_Ioc.mp hqI
      change ¬ ∀ p ∈ q.primeFactors, p^4 ≤ X at hs
      push Not at hs
      obtain ⟨p,hp,high⟩ := hs
      obtain ⟨hprime,hdvd,hq0⟩ := Nat.mem_primeFactors.mp hp
      let d := q/p
      have eq : d*p=q := Nat.div_mul_cancel hdvd
      have hr : (q:ℝ) ≤ Real.sqrt X := by
        rw [Real.sqrt_eq_rpow]
        exact (Nat.le_floor_iff (by positivity)).mp hhi
      have hsq : q^2 ≤ X := by
        exact_mod_cast (show (q:ℝ)^2 ≤ (X:ℝ) by
          have h := pow_le_pow_left₀ (Nat.cast_nonneg q) hr 2
          simpa only [Real.sq_sqrt (Nat.cast_nonneg X)] using h)
      have hdp : d ≤ p := by
        by_contra! h
        have hm : p^2 ≤ d*p := by rw [pow_two]; gcongr
        have h4 : p^4 ≤ q^2 := by
          calc
            p^4 = (p^2)^2 := by ring
            _ ≤ q^2 := Nat.pow_le_pow_left (by simpa only [eq] using hm) 2
        omega
      have hd4 : d^4 ≤ X := by
        calc
          d^4 = (d*d)^2 := by ring
          _ ≤ (d*p)^2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left d hdp) 2
          _ = q^2 := by rw [eq]
          _ ≤ X := hsq
      have hpq : p ≤ q := Nat.le_of_dvd (by omega) hdvd
      have dpos : 0 < d := Nat.div_pos hpq hprime.pos
      refine mem_image.mpr ⟨(d,p), ?_, eq⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨dpos, hdp.trans (hpq.trans hhi)⟩,
        mem_Icc.mpr ⟨hprime.pos,hpq.trans hhi⟩⟩, hprime,high,hd4,by simpa only [eq] using hl,by simpa only [eq] using hhi⟩
    change ∑ q ∈ bad, err X q ≤ ∑ z ∈ pairs, err X (prod z)
    calc
      _ ≤ ∑ q ∈ pairs.image prod, err X q :=
        sum_le_sum_of_subset_of_nonneg cover (fun q _ _ => (endpointError X q).coe_nonneg)
      _ ≤ _ := by
        exact Finset.sum_image_le_of_nonneg (fun q _ => (endpointError X q).coe_nonneg)
  intro A hA
  obtain ⟨b,C,hb,hC,N,hclassic⟩ := classical_range A hA
  obtain ⟨Cs,hCs,Ns,hs⟩ := hSmooth A b hA hb
  obtain ⟨Cp,hCp,Np,hp⟩ := hSwitched A b hA hb
  refine ⟨C+Cs+Cp, max N (max Ns Np), by positivity, ?_⟩
  intro X hX
  have hN : N ≤ X := (le_max_left _ _).trans hX
  have hNs : Ns ≤ X := (le_max_left Ns Np).trans ((le_max_right N _).trans hX)
  have hNp : Np ≤ X := (le_max_right Ns Np).trans ((le_max_right N _).trans hX)
  let lo := ⌊(X:ℝ)^(1/2:ℝ)/(Real.log X)^b⌋₊
  let hi := ⌊(X:ℝ)^(1/2:ℝ)⌋₊
  let E := err X
  let Z := (X:ℝ)/(Real.log X)^A
  have hsmall : (∑ q ∈ Icc 1 lo, E q) ≤ C*Z := by
    simpa only [lo,E,Z,mul_div_assoc] using hclassic X hN
  have hs' : (∑ q ∈ (Ioc lo hi).filter (smooth X), E q) ≤ Cs*Z := by
    simpa only [lo,hi,E,Z,err,smooth,
      endpointError,residuePrefix,residueSlice,Nat.floor_natCast,mul_div_assoc] using hs X hNs
  have hp' : (∑ z ∈ factorPairs X lo hi, E (z.1*z.2)) ≤ Cp*Z := by
    simpa only [lo,hi,E,Z,err,factorPairs,
      endpointError,residuePrefix,residueSlice,Nat.floor_natCast,mul_div_assoc] using hp X hNp
  have hlarge := (switched X lo).trans hp'
  have split := Finset.sum_filter_add_sum_filter_not (Ioc lo hi) (smooth X) E
  refine ⟨E, fun q hq a ha => majorize X q a (mem_Icc.mp hq).1 ha, ?_⟩
  change (∑ q ∈ Icc 1 hi, E q) ≤ (C+Cs+Cp)*X/(Real.log X)^A
  rw [mul_div_assoc]
  change (∑ q ∈ Icc 1 hi, E q) ≤ (C+Cs+Cp)*Z
  have join := join_bands X lo hi
  change (∑ q ∈ Icc 1 hi, E q) ≤ (∑ q ∈ Icc 1 lo, E q) + ∑ q ∈ Ioc lo hi, E q at join
  change (∑ q ∈ (Ioc lo hi).filter (fun q => ¬ smooth X q), E q) ≤ Cp*Z at hlarge
  linarith only [join,split,hsmall,hs',hlarge]
