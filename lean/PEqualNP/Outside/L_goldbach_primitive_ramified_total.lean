import Mathlib

private theorem central_power_count (n p : ℕ) (_hn : 0 < n) (hp : p.Prime) :
    ((Finset.Icc 1 (Nat.log 2 n)).filter
      (fun a => n ≤ 3 * p ^ a ∧ 3 * p ^ a ≤ 2 * n)).card ≤
      (if p = 2 then 2 else 1) := by
  let S := (Finset.Icc 1 (Nat.log 2 n)).filter
    (fun a => n ≤ 3 * p ^ a ∧ 3 * p ^ a ≤ 2 * n)
  let k : ℕ := if p = 2 then 2 else 1
  change S.card ≤ k
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := S.min'_mem hS
    have hlower : n ≤ 3 * p ^ m := (Finset.mem_filter.mp hm).2.1
    have hp2 := hp.two_le
    have hgrowth : 3 ≤ p ^ k := by
      by_cases h : p = 2
      · norm_num [k, h]
      · simpa [k, h] using (show 3 ≤ p by omega)
    have hsub : S ⊆ Finset.Ico m (m + k) := by
      intro a ha
      refine Finset.mem_Ico.mpr ⟨S.min'_le a ha, ?_⟩
      by_contra! hgap
      have hupper := (Finset.mem_filter.mp ha).2.2
      have hpos : 0 < p ^ m := pow_pos hp.pos _
      have hmul : p ^ m * 3 ≤ p ^ a := calc
        p ^ m * 3 ≤ p ^ m * p ^ k := Nat.mul_le_mul_left _ hgrowth
        _ = p ^ (m + k) := (pow_add p m k).symm
        _ ≤ p ^ a := pow_le_pow_right₀ (by omega) hgap
      omega
    calc
      S.card ≤ (Finset.Ico m (m + k)).card := Finset.card_le_card hsub
      _ = k := by rw [Nat.card_Ico]; omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

theorem PEqualNP.Outside.L_goldbach_primitive_ramified_total :
    ∀ n : ℕ, 2≤n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n), ArithmeticFunction.vonMangoldt k) ≤ 2*Real.log (n:ℝ) := by
  intro n hn
  classical
  let S := (Finset.range (n + 1)).filter
    (fun k => n ≤ 3 * k ∧ 3 * k ≤ 2 * n ∧ ¬k.Coprime n)
  let T := S.filter IsPrimePow
  let P := n.primeFactors
  let A := Finset.Icc 1 (Nat.log 2 n)
  let B : ℕ → Finset ℕ := fun p =>
    A.filter (fun a => n ≤ 3 * p ^ a ∧ 3 * p ^ a ≤ 2 * n)
  let U := (P ×ˢ A).filter
    (fun pa => n ≤ 3 * pa.1 ^ pa.2 ∧ 3 * pa.1 ^ pa.2 ≤ 2 * n)
  have hn0 : n ≠ 0 := by omega
  have hTS : T = U.image (fun pa : ℕ × ℕ => pa.1 ^ pa.2) := by
    ext k
    constructor
    · intro hk
      change k ∈ S.filter IsPrimePow at hk
      rcases Finset.mem_filter.mp hk with ⟨hkS, hkPow⟩
      rcases hkPow with ⟨p, a, hp, ha, rfl⟩
      have hpNat : Nat.Prime p := Nat.prime_iff.mpr hp
      have hcentral : n ≤ 3 * p ^ a ∧ 3 * p ^ a ≤ 2 * n ∧ ¬(p ^ a).Coprime n :=
        (Finset.mem_filter.mp hkS).2
      have hpdiv : p ∣ n := by
        rcases Nat.Prime.not_coprime_iff_dvd.mp hcentral.2.2 with ⟨q, hq, hqk, hqn⟩
        have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hpNat).mp (hq.dvd_of_dvd_pow hqk)
        simpa [hqp] using hqn
      have hpow : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hpNat.two_le a
      have ha_log : a ≤ Nat.log 2 n :=
        Nat.le_log_of_pow_le (by norm_num) (by omega)
      have hpMem : p ∈ P := by
        change p ∈ n.primeFactors
        simpa [Nat.mem_primeFactors] using (And.intro hpNat (And.intro hpdiv hn0))
      refine Finset.mem_image.mpr ⟨(p, a), ?_, rfl⟩
      change (p, a) ∈ (P ×ˢ A).filter
        (fun pa => n ≤ 3 * pa.1 ^ pa.2 ∧ 3 * pa.1 ^ pa.2 ≤ 2 * n)
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hpMem, Finset.mem_Icc.mpr ⟨ha, ha_log⟩⟩, ?_⟩
      exact ⟨hcentral.1, hcentral.2.1⟩
    · intro hk
      rcases Finset.mem_image.mp hk with ⟨⟨p, a⟩, hpa, rfl⟩
      have hpa' := Finset.mem_filter.mp hpa
      have hpP : p ∈ P := (Finset.mem_product.mp hpa'.1).1
      have haA : a ∈ A := (Finset.mem_product.mp hpa'.1).2
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpP
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpP
      have ha : 0 < a := (Finset.mem_Icc.mp haA).1
      have hcentral : n ≤ 3 * p ^ a ∧ 3 * p ^ a ≤ 2 * n := hpa'.2
      change p ^ a ∈ S.filter IsPrimePow
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr (by omega), hcentral.1, hcentral.2, ?_⟩
        exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p ha.ne') hpdvd
      · exact ⟨p, a, hp.prime, ha, rfl⟩
  have hinj : Set.InjOn (fun pa : ℕ × ℕ => pa.1 ^ pa.2) U := by
    rintro ⟨p, a⟩ hpa ⟨q, b⟩ hqb h
    have hp : p.Prime := Nat.prime_of_mem_primeFactors
      (Finset.mem_product.mp (Finset.mem_filter.mp hpa).1).1
    have hq : q.Prime := Nat.prime_of_mem_primeFactors
      (Finset.mem_product.mp (Finset.mem_filter.mp hqb).1).1
    have ha : 0 < a := (Finset.mem_Icc.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hpa).1).2).1
    have hb : 0 < b := (Finset.mem_Icc.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hqb).1).2).1
    have hpq := hp.pow_inj' hq ha.ne' hb.ne' h
    exact Prod.ext hpq.1 hpq.2
  have hsum : ∑ k ∈ T, ArithmeticFunction.vonMangoldt k =
      ∑ pa ∈ U, Real.log (pa.1 : ℝ) := by
    rw [hTS, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    rintro ⟨p, a⟩ hpa
    have hpP : p ∈ P := (Finset.mem_product.mp (Finset.mem_filter.mp hpa).1).1
    have haA : a ∈ A := (Finset.mem_product.mp (Finset.mem_filter.mp hpa).1).2
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpP
    have ha : 0 < a := (Finset.mem_Icc.mp haA).1
    rw [ArithmeticFunction.vonMangoldt_apply_pow ha.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hUsum : ∑ pa ∈ U, Real.log (pa.1 : ℝ) =
      ∑ p ∈ P, (B p).card * Real.log (p : ℝ) := by
    dsimp only [U]
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_filter]
    simp [B]
  have hbound : ∑ pa ∈ U, Real.log (pa.1 : ℝ) ≤
      ∑ p ∈ P, (if p = 2 then (2 : ℝ) else 1) * Real.log (p : ℝ) := by
    rw [hUsum]
    apply Finset.sum_le_sum
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hcard : (B p).card ≤ (if p = 2 then 2 else 1) := by
      simpa [B, A] using central_power_count n p (by omega) hprime
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hprime.one_le)
    have hcardR : ((B p).card : ℝ) ≤ (if p = 2 then (2 : ℝ) else 1) := by
      split_ifs with h
      · have hcard' : (B p).card ≤ 2 := by simpa [h] using hcard
        exact_mod_cast hcard'
      · have hcard' : (B p).card ≤ 1 := by simpa [h] using hcard
        exact_mod_cast hcard'
    exact mul_le_mul_of_nonneg_right hcardR hlog
  have hterm : ∀ p ∈ P,
      (if p = 2 then (2 : ℝ) else 1) * Real.log (p : ℝ) ≤
        Real.log (p : ℝ) + (if p = 2 then Real.log 2 else 0) := by
    intro p hp
    split_ifs with h
    · subst p
      ring_nf
      exact le_rfl
    · simp
  have hsplit : ∑ p ∈ P, (if p = 2 then (2 : ℝ) else 1) * Real.log (p : ℝ) ≤
      (∑ p ∈ P, Real.log (p : ℝ)) +
        ∑ p ∈ P, (if p = 2 then Real.log 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hterm
  have hindicator : ∑ p ∈ P, (if p = 2 then Real.log 2 else 0) ≤ Real.log 2 := by
    rw [Finset.sum_ite_eq' P 2 (fun _ => Real.log 2)]
    split_ifs
    · exact le_rfl
    · exact Real.log_nonneg (by norm_num)
  have hlogsum : ∑ p ∈ P, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
    rw [← Real.log_prod (f := fun p : ℕ => (p : ℝ)) (by
      intro p hp
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    have hprod : (∏ p ∈ P, p) ≤ n :=
      Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    have hpos : 0 < ∏ p ∈ P, (p : ℝ) :=
      Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hprodR : (∏ p ∈ P, (p : ℝ)) ≤ (n : ℝ) := by
      calc
        (∏ p ∈ P, (p : ℝ)) = ((∏ p ∈ P, p : ℕ) : ℝ) := by simp
        _ ≤ (n : ℝ) := by exact_mod_cast hprod
    exact Real.log_le_log hpos hprodR
  have h2n : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  change (∑ k ∈ S, ArithmeticFunction.vonMangoldt k) ≤ 2 * Real.log (n : ℝ)
  calc
    ∑ k ∈ S, ArithmeticFunction.vonMangoldt k =
        ∑ k ∈ T, ArithmeticFunction.vonMangoldt k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hnot
      have hnotPow : ¬ IsPrimePow k := by
        intro hpow
        exact hnot (Finset.mem_filter.mpr ⟨hk, hpow⟩)
      exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnotPow
    _ = ∑ pa ∈ U, Real.log (pa.1 : ℝ) := hsum
    _ ≤ ∑ p ∈ P, (if p = 2 then (2 : ℝ) else 1) * Real.log (p : ℝ) := hbound
    _ ≤ (∑ p ∈ P, Real.log (p : ℝ)) +
        ∑ p ∈ P, (if p = 2 then Real.log 2 else 0) := hsplit
    _ ≤ Real.log (n : ℝ) + Real.log 2 := add_le_add hlogsum hindicator
    _ ≤ 2 * Real.log (n : ℝ) := by linarith
