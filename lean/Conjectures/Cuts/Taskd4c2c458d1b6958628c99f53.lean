import Mathlib

open scoped BigOperators
open Finset

namespace Conjectures.Cuts.Taskd4c2c458Proof

lemma nat_prod_dvd_of_coprime {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ} {n : ℕ}
    (hcop : (s : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j)))
    (hdvd : ∀ i ∈ s, f i ∣ n) : (∏ i ∈ s, f i) ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    have hcop_t : (t : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j)) :=
      hcop.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    have ht_dvd : (∏ i ∈ t, f i) ∣ n := ih hcop_t (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))
    have ha_dvd : f a ∣ n := hdvd a (Finset.mem_insert_self a t)
    have ha_cop : Nat.Coprime (f a) (∏ i ∈ t, f i) :=
      Nat.Coprime.prod_right (fun i hi =>
        hcop (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi) (fun h => hat (h ▸ hi)))
    exact ha_cop.mul_dvd_of_dvd_of_dvd ha_dvd ht_dvd

lemma nat_prime_dvd_finset_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (hdvd : p ∣ ∏ i ∈ s, f i) : ∃ i ∈ s, p ∣ f i := by
  induction s using Finset.induction_on with
  | empty => simp at hdvd; exact absurd hdvd hp.ne_one
  | insert a t hat ih =>
    rw [Finset.prod_insert hat] at hdvd
    rcases hp.dvd_mul.mp hdvd with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a t, h1⟩
    · obtain ⟨i, hi, hid⟩ := ih h2
      exact ⟨i, Finset.mem_insert_of_mem hi, hid⟩

lemma factorization_eq_zero_of_not_mem_primeFactors {m r : ℕ} (hr : r ∉ m.primeFactors) :
    m.factorization r = 0 :=
  Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])

lemma finsupp_sum_apply_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ →₀ ℕ) (p : ℕ) :
    (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat, Finsupp.add_apply, ih]

lemma prod_primeFactors_pow_factorization {m : ℕ} (hm : m ≠ 0) :
    ∏ r ∈ m.primeFactors, r ^ (m.factorization r) = m := by
  have hprod_ne : ∏ r ∈ m.primeFactors, r ^ (m.factorization r) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun r hr => pow_pos (Nat.mem_primeFactors.mp hr).1.pos _))
  apply Nat.eq_of_factorization_eq hprod_ne hm
  intro p
  rw [Nat.factorization_prod (fun r hr => ne_of_gt (pow_pos (Nat.mem_primeFactors.mp hr).1.pos _)),
    finsupp_sum_apply_nat]
  by_cases hp : p ∈ m.primeFactors
  · rw [Finset.sum_eq_single p]
    · have hpP := (Nat.mem_primeFactors.mp hp).1
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hpP.factorization_self, mul_one]
    · intro r hr hrp
      have hrP := (Nat.mem_primeFactors.mp hr).1
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hrP.factorization,
        Finsupp.single_eq_of_ne (Ne.symm hrp), mul_zero]
    · intro h; exact absurd hp h
  · rw [Finset.sum_eq_zero]
    · exact (factorization_eq_zero_of_not_mem_primeFactors hp).symm
    · intro r hr
      have hrP := (Nat.mem_primeFactors.mp hr).1
      have hrne : r ≠ p := fun h => hp (h ▸ hr)
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hrP.factorization,
        Finsupp.single_eq_of_ne hrne.symm, mul_zero]

lemma real_prod_le_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.prod_insert hat]
    have hft : ∀ i ∈ t, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfgt : ∀ i ∈ t, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul (hfg a (Finset.mem_insert_self a t)) (ih hft hfgt)
      (Finset.prod_nonneg hft) (le_trans (hf a (Finset.mem_insert_self a t)) (hfg a (Finset.mem_insert_self a t)))

lemma sum_biUnion_le_sum {ι α : Type*} [DecidableEq α] {s : Finset ι} {t : ι → Finset α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert has]
    have hu : ∑ x ∈ t a ∪ s.biUnion t, f x ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
      have h1 := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have h2 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg (fun x _ => hf x)
      linarith
    linarith

/-!
## Part 1: Elementary Chebyshev bound `theta(n) ≤ n * log 4`
-/

lemma prod_primes_Ioc_dvd_choose (m : ℕ) :
    (∏ p ∈ (Finset.Ioc m (2 * m)).filter Nat.Prime, p) ∣ Nat.choose (2 * m) m := by
  have hcop : Set.Pairwise (↑((Finset.Ioc m (2 * m)).filter Nat.Prime) : Set ℕ) Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq
  apply nat_prod_dvd_of_coprime hcop
  intro p hp
  have hpI : m < p ∧ p ≤ 2 * m := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hmul : Nat.choose (2 * m) m * (m.factorial * m.factorial) = (2 * m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
    have hsub : 2 * m - m = m := by omega
    rw [hsub] at h
    linarith
  have hdvd_num : p ∣ (2 * m).factorial := hpP.dvd_factorial.mpr hpI.2
  have hndvd_den : ¬ p ∣ m.factorial := fun h => by have := hpP.dvd_factorial.mp h; omega
  rw [← hmul] at hdvd_num
  rcases hpP.dvd_mul.mp hdvd_num with h1 | h2
  · exact h1
  · rcases hpP.dvd_mul.mp h2 with h3 | h4
    · exact absurd h3 hndvd_den
    · exact absurd h4 hndvd_den

lemma prod_primes_Ioc_dvd_choose_odd (m : ℕ) :
    (∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p) ∣ Nat.choose (2 * m + 1) m := by
  have hcop : Set.Pairwise (↑((Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime) : Set ℕ) Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq
  apply nat_prod_dvd_of_coprime hcop
  intro p hp
  have hpI : m + 1 < p ∧ p ≤ 2 * m + 1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hmul : Nat.choose (2 * m + 1) m * (m.factorial * (m + 1).factorial) = (2 * m + 1).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m + 1)
    have hsub : 2 * m + 1 - m = m + 1 := by omega
    rw [hsub] at h
    linarith
  have hdvd_num : p ∣ (2 * m + 1).factorial := hpP.dvd_factorial.mpr hpI.2
  have hndvd1 : ¬ p ∣ m.factorial := fun h => by have := hpP.dvd_factorial.mp h; omega
  have hndvd2 : ¬ p ∣ (m + 1).factorial := fun h => by have := hpP.dvd_factorial.mp h; omega
  rw [← hmul] at hdvd_num
  rcases hpP.dvd_mul.mp hdvd_num with h1 | h2
  · exact h1
  · rcases hpP.dvd_mul.mp h2 with h3 | h4
    · exact absurd h3 hndvd1
    · exact absurd h4 hndvd2

lemma choose_two_mul_le (m : ℕ) : Nat.choose (2 * m) m ≤ 4 ^ m := by
  have hsum : ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) k = 2 ^ (2 * m) :=
    Nat.sum_range_choose (2 * m)
  have hle : Nat.choose (2 * m) m ≤ ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hpow : 2 ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  omega

lemma choose_two_mul_add_one_le (m : ℕ) : Nat.choose (2 * m + 1) m ≤ 4 ^ m := by
  have hsym : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    have h := Nat.choose_symm (by omega : m ≤ 2 * m + 1)
    have hsub : 2 * m + 1 - m = m + 1 := by omega
    rw [hsub] at h
    exact h
  have hsum : ∑ k ∈ Finset.range (2 * m + 2), Nat.choose (2 * m + 1) k = 2 ^ (2 * m + 1) :=
    Nat.sum_range_choose (2 * m + 1)
  have hsub : ({m, m + 1} : Finset ℕ) ⊆ Finset.range (2 * m + 2) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have hle : ∑ k ∈ ({m, m + 1} : Finset ℕ), Nat.choose (2 * m + 1) k ≤
      ∑ k ∈ Finset.range (2 * m + 2), Nat.choose (2 * m + 1) k :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair (by omega : m ≠ m + 1), hsym, hsum] at hle
  have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by rw [pow_succ, pow_mul]; norm_num; ring
  omega

lemma prod_primes_le_four_pow (n : ℕ) :
    (∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p) ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n ≤ 1
    · have hempty : (Finset.Icc 2 n).filter Nat.Prime = ∅ := by
        ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [hempty, Finset.prod_empty]
      exact Nat.one_le_pow n 4 (by norm_num)
    · push_neg at hn
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have h2m : n = 2 * m := by omega
        subst h2m
        have hsplit : (Finset.Icc 2 (2 * m)).filter Nat.Prime =
            (Finset.Icc 2 m).filter Nat.Prime ∪ (Finset.Ioc m (2 * m)).filter Nat.Prime := by
          ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
          constructor
          · intro ⟨⟨h1, h2⟩, hp⟩
            by_cases hpm : p ≤ m
            · left; exact ⟨⟨h1, hpm⟩, hp⟩
            · right; exact ⟨⟨by omega, h2⟩, hp⟩
          · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
            · exact ⟨⟨h1, by omega⟩, hp⟩
            · exact ⟨⟨by omega, h2⟩, hp⟩
        have hdisj : Disjoint ((Finset.Icc 2 m).filter Nat.Prime)
            ((Finset.Ioc m (2 * m)).filter Nat.Prime) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
          have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).1
          omega
        rw [hsplit, Finset.prod_union hdisj]
        have h1 := ih m (by omega)
        have h2 : (∏ p ∈ (Finset.Ioc m (2 * m)).filter Nat.Prime, p) ≤ 4 ^ m :=
          le_trans (Nat.le_of_dvd (Nat.choose_pos (by omega)) (prod_primes_Ioc_dvd_choose m))
            (choose_two_mul_le m)
        calc (∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, p) *
              (∏ p ∈ (Finset.Ioc m (2 * m)).filter Nat.Prime, p)
            ≤ 4 ^ m * 4 ^ m := Nat.mul_le_mul h1 h2
          _ = 4 ^ (2 * m) := by rw [← pow_add, two_mul]
      · subst hm
        have hsplit : (Finset.Icc 2 (2 * m + 1)).filter Nat.Prime =
            (Finset.Icc 2 (m + 1)).filter Nat.Prime ∪ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime := by
          ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
          constructor
          · intro ⟨⟨h1, h2⟩, hp⟩
            by_cases hpm : p ≤ m + 1
            · left; exact ⟨⟨h1, hpm⟩, hp⟩
            · right; exact ⟨⟨by omega, h2⟩, hp⟩
          · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
            · exact ⟨⟨h1, by omega⟩, hp⟩
            · exact ⟨⟨by omega, h2⟩, hp⟩
        have hdisj : Disjoint ((Finset.Icc 2 (m + 1)).filter Nat.Prime)
            ((Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
          have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).1
          omega
        rw [hsplit, Finset.prod_union hdisj]
        have h1 := ih (m + 1) (by omega)
        have h2 : (∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p) ≤ 4 ^ m :=
          le_trans (Nat.le_of_dvd (Nat.choose_pos (by omega)) (prod_primes_Ioc_dvd_choose_odd m))
            (choose_two_mul_add_one_le m)
        calc (∏ p ∈ (Finset.Icc 2 (m + 1)).filter Nat.Prime, p) *
              (∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p)
            ≤ 4 ^ (m + 1) * 4 ^ m := Nat.mul_le_mul h1 h2
          _ = 4 ^ (2 * m + 1) := by rw [← pow_add]; congr 1; omega

lemma sum_log_primes_le (n : ℕ) :
    ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.log (p : ℝ) ≤ (n : ℝ) * Real.log 4 := by
  have hprod := prod_primes_le_four_pow n
  have hprod_pos : (0 : ℝ) < ((∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => Nat.Prime.pos (Finset.mem_filter.mp hp).2)
  have hlog : Real.log ((∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p : ℕ) : ℝ) ≤
      Real.log ((4 ^ n : ℕ) : ℝ) :=
    Real.log_le_log hprod_pos (by exact_mod_cast hprod)
  have hL : Real.log ((∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p : ℕ) : ℝ) =
      ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact ne_of_gt (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
  have hR : Real.log ((4 ^ n : ℕ) : ℝ) = (n : ℝ) * Real.log 4 := by
    rw [Nat.cast_pow, Real.log_pow]; norm_num
  linarith

lemma sum_inv_primes_Ioc_le {A B : ℕ} (hA : 2 ≤ A) :
    ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      ((B : ℝ) * Real.log 4) / ((A : ℝ) * Real.log (A : ℝ)) := by
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hlogA_pos : (0 : ℝ) < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have hsub : (Finset.Ioc A B).filter Nat.Prime ⊆ (Finset.Icc 2 B).filter Nat.Prime := by
    intro p hp
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2⟩, (Finset.mem_filter.mp hp).2⟩
  have h1 : (A : ℝ) * Real.log (A : ℝ) *
      (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
      ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hAp : (A : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_of_lt hpI.1
    have hlog_le : Real.log (A : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log hApos hAp
    have hdiv : (A : ℝ) / (p : ℝ) ≤ 1 := (div_le_one hppos).mpr hAp
    calc (A : ℝ) * Real.log (A : ℝ) * (1 / (p : ℝ))
        = ((A : ℝ) / (p : ℝ)) * Real.log (A : ℝ) := by ring
      _ ≤ 1 * Real.log (p : ℝ) := mul_le_mul hdiv hlog_le (le_of_lt hlogA_pos) zero_le_one
      _ = Real.log (p : ℝ) := one_mul _
  have h2 : ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log (p : ℝ) ≤
      ∑ p ∈ (Finset.Icc 2 B).filter Nat.Prime, Real.log (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast le_of_lt (Finset.mem_filter.mp hp).2.one_lt))
  have h3 := sum_log_primes_le B
  rw [le_div_iff₀ (mul_pos hApos hlogA_pos)]
  linarith

lemma sum_inv_primes_dyadic {T B K : ℕ} (hT : 2 ≤ T) (hB : B ≤ 2 ^ K * T) :
    ∑ p ∈ (Finset.Ioc T B).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      (K : ℝ) * (2 * Real.log 4) / Real.log (T : ℝ) := by
  have hlogT_pos : (0 : ℝ) < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hcov : (Finset.Ioc T B).filter Nat.Prime ⊆
      (Finset.range K).biUnion (fun k => (Finset.Ioc (2 ^ k * T) (2 ^ (k + 1) * T)).filter Nat.Prime) := by
    intro p hp
    have hpI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hpP := (Finset.mem_filter.mp hp).2
    have hex : ∃ k < K, 2 ^ k * T < p ∧ p ≤ 2 ^ (k + 1) * T := by
      have hp_le : p ≤ 2 ^ K * T := le_trans hpI.2 hB
      have hp_gt : T < p := hpI.1
      clear hp hpP hB hpI
      induction K with
      | zero => simp at hp_le; omega
      | succ K' ih =>
        by_cases hle : p ≤ 2 ^ K' * T
        · obtain ⟨k, hk, h1, h2⟩ := ih hle
          exact ⟨k, by omega, h1, h2⟩
        · exact ⟨K', by omega, by omega, hp_le⟩
    rcases hex with ⟨k, hk, h1, h2⟩
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk,
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1, h2⟩, hpP⟩⟩
  calc ∑ p ∈ (Finset.Ioc T B).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ (Finset.range K).biUnion (fun k =>
          (Finset.Ioc (2 ^ k * T) (2 ^ (k + 1) * T)).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcov (fun p _ _ => by positivity)
    _ ≤ ∑ k ∈ Finset.range K,
          ∑ p ∈ (Finset.Ioc (2 ^ k * T) (2 ^ (k + 1) * T)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
        sum_biUnion_le_sum (fun _ => by positivity)
    _ ≤ ∑ _k ∈ Finset.range K, (2 * Real.log 4) / Real.log (T : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        have hAk : 2 ≤ 2 ^ k * T := by
          have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num); nlinarith
        have hstep := sum_inv_primes_Ioc_le (A := 2 ^ k * T) (B := 2 ^ (k + 1) * T) hAk
        have hApos : (0 : ℝ) < ((2 ^ k * T : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 ^ k * T)
        have hTleA : (T : ℝ) ≤ ((2 ^ k * T : ℕ) : ℝ) := by
          have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
          exact_mod_cast (by nlinarith : T ≤ 2 ^ k * T)
        have hlogle : Real.log (T : ℝ) ≤ Real.log ((2 ^ k * T : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < T)) hTleA
        have hcast : ((2 ^ (k + 1) * T : ℕ) : ℝ) = 2 * ((2 ^ k * T : ℕ) : ℝ) := by
          push_cast; rw [pow_succ]; ring
        calc ∑ p ∈ (Finset.Ioc (2 ^ k * T) (2 ^ (k + 1) * T)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
            ≤ ((2 ^ (k + 1) * T : ℕ) : ℝ) * Real.log 4 /
                (((2 ^ k * T : ℕ) : ℝ) * Real.log ((2 ^ k * T : ℕ) : ℝ)) := hstep
          _ = (2 * Real.log 4) / Real.log ((2 ^ k * T : ℕ) : ℝ) := by
              rw [hcast]; field_simp [ne_of_gt hApos]
          _ ≤ (2 * Real.log 4) / Real.log (T : ℝ) :=
              div_le_div_of_nonneg_left (by positivity) hlogT_pos hlogle
    _ = (K : ℝ) * (2 * Real.log 4) / Real.log (T : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-!
## Part 2: Elementary Mertens lower bound on `∏_{3 ≤ p ≤ m} (1 - 2/p)`
-/

lemma prime_pow_div_dvd_factorial {p m : ℕ} (hp : 0 < p) : p ^ (m / p) ∣ m.factorial := by
  have hsub : (Finset.Icc 1 (m / p)).image (fun k => k * p) ⊆ Finset.Icc 1 m := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    have hk' := Finset.mem_Icc.mp hk
    have h1 : 1 ≤ k * p := Nat.mul_pos hk'.1 hp
    have h2 : k * p ≤ m := le_trans (Nat.mul_le_mul_right p hk'.2) (Nat.div_mul_le_self m p)
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hinj : Set.InjOn (fun k => k * p) (Finset.Icc 1 (m / p) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_right hp hab
  have hprod_eq : ∏ x ∈ (Finset.Icc 1 (m / p)).image (fun k => k * p), x =
      (∏ k ∈ Finset.Icc 1 (m / p), k) * p ^ (m / p) := by
    rw [Finset.prod_image (fun a ha b hb hab => hinj ha hb hab), Finset.prod_mul_distrib,
      Finset.prod_const, Nat.card_Icc]
    simp
  have hdvd1 : (∏ x ∈ (Finset.Icc 1 (m / p)).image (fun k => k * p), x) ∣ ∏ x ∈ Finset.Icc 1 m, x :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hfac : ∀ k : ℕ, ∏ x ∈ Finset.Icc 1 k, x = k.factorial := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), ih, Nat.factorial_succ, mul_comm]
  rw [hprod_eq, hfac m] at hdvd1
  exact dvd_trans (dvd_mul_left _ _) hdvd1

lemma prod_prime_pow_div_dvd_factorial (m : ℕ) :
    (∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, p ^ (m / p)) ∣ m.factorial := by
  have hcop : Set.Pairwise (↑((Finset.Icc 2 m).filter Nat.Prime) : Set ℕ)
      (fun p q => Nat.Coprime (p ^ (m / p)) (q ^ (m / q))) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq).pow _ _
  apply nat_prod_dvd_of_coprime hcop
  intro p hp
  exact prime_pow_div_dvd_factorial (Finset.mem_filter.mp hp).2.pos

lemma sum_log_div_prime_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (m : ℝ) + Real.log 4 := by
  have hdvd := prod_prime_pow_div_dvd_factorial m
  have hle_fac : (∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, p ^ (m / p)) ≤ m.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos m) hdvd
  have hfac_le : m.factorial ≤ m ^ m := Nat.factorial_le_pow m
  have hprod_pos : (0 : ℝ) < ((∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, p ^ (m / p) : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _)
  have hlog : Real.log ((∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, p ^ (m / p) : ℕ) : ℝ) ≤
      Real.log ((m ^ m : ℕ) : ℝ) :=
    Real.log_le_log hprod_pos (by exact_mod_cast le_trans hle_fac hfac_le)
  have hL : Real.log ((∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, p ^ (m / p) : ℕ) : ℝ) =
      ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, ((m / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p _
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      exact ne_of_gt (by exact_mod_cast pow_pos (Finset.mem_filter.mp hp).2.pos _)
  have hR : Real.log ((m ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log (m : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hdiff : (m : ℝ) * (∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) -
      ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, Real.log (p : ℝ) ≤
      ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, ((m / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpP := (Finset.mem_filter.mp hp).2
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpP.pos
    have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast le_of_lt hpP.one_lt)
    have hdiv_ge : (m : ℝ) / (p : ℝ) - 1 ≤ ((m / p : ℕ) : ℝ) := by
      have h1 : m < p * (m / p + 1) := Nat.lt_mul_div_succ m hpP.pos
      have h2 : (m : ℝ) < (((m / p : ℕ) : ℝ) + 1) * (p : ℝ) := by
        have : (m : ℝ) < (p : ℝ) * (((m / p : ℕ) : ℝ) + 1) := by exact_mod_cast h1
        linarith
      have h3 : (m : ℝ) / (p : ℝ) < ((m / p : ℕ) : ℝ) + 1 := (div_lt_iff₀ hp_pos).mpr h2
      linarith
    calc (m : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ)
        = ((m : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) := by ring
      _ ≤ ((m / p : ℕ) : ℝ) * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hdiv_ge hlog_nn
  have htheta := sum_log_primes_le m
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  nlinarith

lemma log_log_diff_ge {k : ℕ} (hk : 2 ≤ k) :
    (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ) ≤
      Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)) := by
  have ha : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hb : 0 < Real.log ((k + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k + 1))
  have h1 : Real.log (Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ)) ≤
      Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at h1
  have h2 : Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ) - 1 =
      -((Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ)) := by
    field_simp [ne_of_gt hb]; ring
  linarith

/-- Mertens upper bound: `∑_{p ≤ m} 1/p ≤ log(log m) + 6` for `m ≥ 3`. -/
lemma sum_inv_primes_le_log_log {m : ℕ} (hm : 3 ≤ m) :
    ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      Real.log (Real.log (m : ℝ)) + 6 := by
  let S1 : ℕ → ℝ := fun k => ∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
  have hS1_diff : ∀ k ≥ 2, S1 k - S1 (k - 1) =
      if Nat.Prime k then Real.log (k : ℝ) / (k : ℝ) else 0 := by
    intro k hk
    have hsplit : (Finset.Icc 2 k).filter Nat.Prime =
        (Finset.Icc 2 (k - 1)).filter Nat.Prime ∪ (if Nat.Prime k then {k} else ∅) := by
      ext x
      by_cases hpk : Nat.Prime k
      · simp only [hpk, ↓reduceIte, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
        constructor
        · intro ⟨⟨h1, h2⟩, hpx⟩
          by_cases hxk : x = k
          · right; exact hxk
          · left; exact ⟨⟨h1, by omega⟩, hpx⟩
        · rintro (⟨⟨h1, h2⟩, hpx⟩ | rfl)
          · exact ⟨⟨h1, by omega⟩, hpx⟩
          · exact ⟨⟨hk, le_rfl⟩, hpk⟩
      · simp only [hpk, ↓reduceIte, Finset.union_empty, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro ⟨⟨h1, h2⟩, hpx⟩
          have hne : x ≠ k := fun h => hpk (h ▸ hpx)
          exact ⟨⟨h1, by omega⟩, hpx⟩
        · intro ⟨⟨h1, h2⟩, hpx⟩
          exact ⟨⟨h1, by omega⟩, hpx⟩
    have hdisj : Disjoint ((Finset.Icc 2 (k - 1)).filter Nat.Prime) (if Nat.Prime k then {k} else ∅) := by
      by_cases hpk : Nat.Prime k
      · simp only [hpk, ↓reduceIte, Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_Icc]
        omega
      · rw [if_neg hpk]; exact Finset.disjoint_empty_right _
    dsimp only [S1]
    rw [hsplit, Finset.sum_union hdisj]
    by_cases hpk : Nat.Prime k
    · simp [hpk]
    · simp [hpk]
  have hLHS : ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
      ∑ k ∈ Finset.Icc 2 m, (S1 k - S1 (k - 1)) / Real.log (k : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [hS1_diff k hk2]
    by_cases hpk : Nat.Prime k
    · have hlogne : Real.log (k : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < k)))
      rw [if_pos hpk, if_pos hpk]
      field_simp [hlogne]
    · simp [hpk]
  -- Abel summation
  have hS1_1 : S1 1 = 0 := by
    dsimp only [S1]
    have : (Finset.Icc 2 1).filter Nat.Prime = ∅ := by ext x; simp
    rw [this, Finset.sum_empty]
  have habel : ∑ k ∈ Finset.Icc 2 m, (S1 k - S1 (k - 1)) / Real.log (k : ℝ) =
      S1 m / Real.log (m : ℝ) +
      ∑ k ∈ Finset.Icc 2 (m - 1), S1 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
    have hsplit_sum : ∑ k ∈ Finset.Icc 2 m, (S1 k - S1 (k - 1)) / Real.log (k : ℝ) =
        (∑ k ∈ Finset.Icc 2 m, S1 k / Real.log (k : ℝ)) -
        (∑ k ∈ Finset.Icc 2 m, S1 (k - 1) / Real.log (k : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hsplit_sum]
    have h1 : ∑ k ∈ Finset.Icc 2 m, S1 k / Real.log (k : ℝ) =
        S1 m / Real.log (m : ℝ) + ∑ k ∈ Finset.Icc 2 (m - 1), S1 k / Real.log (k : ℝ) := by
      have hm_eq : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hm_eq, Finset.sum_Icc_succ_top (by omega : 2 ≤ (m - 1) + 1)]
      rw [← hm_eq]; ring
    have h2 : ∑ k ∈ Finset.Icc 2 m, S1 (k - 1) / Real.log (k : ℝ) =
        ∑ k ∈ Finset.Icc 2 (m - 1), S1 k / Real.log ((k + 1 : ℕ) : ℝ) := by
      have hm2 : Finset.Icc 2 m = insert 2 (Finset.Icc 3 m) := by ext x; simp; omega
      rw [hm2, Finset.sum_insert (by simp)]
      have hfirst : S1 (2 - 1) / Real.log ((2 : ℕ) : ℝ) = 0 := by simp [hS1_1]
      rw [hfirst, zero_add]
      apply Finset.sum_bij (fun k _ => k - 1)
      · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
      · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
      · intro b hb; refine ⟨b + 1, ?_, by omega⟩; simp only [Finset.mem_Icc] at hb ⊢; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk
        have hkeq : k - 1 + 1 = k := by omega
        rw [hkeq]
    rw [h1, h2]
    have h3 : (∑ k ∈ Finset.Icc 2 (m - 1), S1 k / Real.log (k : ℝ)) -
        (∑ k ∈ Finset.Icc 2 (m - 1), S1 k / Real.log ((k + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.Icc 2 (m - 1), S1 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hLHS, habel]
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; ring
  have hlog2_le : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hterm1 : S1 m / Real.log (m : ℝ) ≤ 1 + Real.log 4 / Real.log 2 := by
    have hlogm : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ m))
    have hlogm_pos : 0 < Real.log (m : ℝ) := lt_of_lt_of_le (by linarith) hlogm
    have hS1m := sum_log_div_prime_le m (by omega)
    calc S1 m / Real.log (m : ℝ)
        ≤ (Real.log (m : ℝ) + Real.log 4) / Real.log (m : ℝ) :=
          div_le_div_of_nonneg_right hS1m (le_of_lt hlogm_pos)
      _ = 1 + Real.log 4 / Real.log (m : ℝ) := by field_simp [ne_of_gt hlogm_pos]
      _ ≤ 1 + Real.log 4 / Real.log 2 := by
          have : Real.log 4 / Real.log (m : ℝ) ≤ Real.log 4 / Real.log 2 :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (by linarith) hlogm
          linarith
  have hterm2 : ∑ k ∈ Finset.Icc 2 (m - 1),
      S1 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
      (Real.log (Real.log (m : ℝ)) - Real.log (Real.log 2)) + Real.log 4 / Real.log 2 := by
    have hstep : ∀ k ∈ Finset.Icc 2 (m - 1),
        S1 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
        (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
        Real.log 4 * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have ha : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
      have hb : 0 < Real.log ((k + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k + 1))
      have hle_ab : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast (by omega : k ≤ k + 1))
      have hdiff_nn : 0 ≤ 1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ) := by
        have := one_div_le_one_div_of_le ha hle_ab; linarith
      have hS1k := sum_log_div_prime_le k (by omega)
      have h1 : S1 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
          (Real.log (k : ℝ) + Real.log 4) * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hS1k hdiff_nn
      have h2 : Real.log (k : ℝ) * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
          (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) / Real.log ((k + 1 : ℕ) : ℝ) := by
        field_simp [ne_of_gt ha, ne_of_gt hb]
      have h3 := log_log_diff_ge hk2
      linarith
    calc ∑ k ∈ Finset.Icc 2 (m - 1), S1 k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.Icc 2 (m - 1),
            ((Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
             Real.log 4 * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))) :=
          Finset.sum_le_sum hstep
      _ = (∑ k ∈ Finset.Icc 2 (m - 1),
            (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)))) +
          Real.log 4 * (∑ k ∈ Finset.Icc 2 (m - 1),
            (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (Real.log (Real.log (m : ℝ)) - Real.log (Real.log 2)) + Real.log 4 / Real.log 2 := by
          have htele1 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
              ∑ k ∈ Finset.Icc a (b - 1),
                (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) =
              Real.log (Real.log (b : ℝ)) - Real.log (Real.log (a : ℝ)) := by
            intro a b ha hab
            induction b with
            | zero => omega
            | succ b ih =>
              by_cases hEq : a = b + 1
              · subst hEq; simp
              · have hab' : a ≤ b := by omega
                have hsub : b + 1 - 1 = b := by omega
                rw [hsub]
                by_cases ha_eq_b : a = b
                · subst ha_eq_b; simp
                · have hbeq : b = (b - 1) + 1 := by omega
                  conv_lhs => rw [hbeq, Finset.sum_Icc_succ_top (by omega : a ≤ (b - 1) + 1)]
                  rw [← hbeq, ih hab']; ring
          have htele2 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
              ∑ k ∈ Finset.Icc a (b - 1),
                (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
              1 / Real.log (a : ℝ) - 1 / Real.log (b : ℝ) := by
            intro a b ha hab
            induction b with
            | zero => omega
            | succ b ih =>
              by_cases hEq : a = b + 1
              · subst hEq; simp
              · have hab' : a ≤ b := by omega
                have hsub : b + 1 - 1 = b := by omega
                rw [hsub]
                by_cases ha_eq_b : a = b
                · subst ha_eq_b; simp
                · have hbeq : b = (b - 1) + 1 := by omega
                  conv_lhs => rw [hbeq, Finset.sum_Icc_succ_top (by omega : a ≤ (b - 1) + 1)]
                  rw [← hbeq, ih hab']; ring
          rw [htele1 2 m le_rfl (by omega), htele2 2 m le_rfl (by omega)]
          have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
          have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          have : 1 / Real.log (2 : ℝ) - 1 / Real.log (m : ℝ) ≤ 1 / Real.log (2 : ℝ) := by
            have : 0 < 1 / Real.log (m : ℝ) := one_div_pos.mpr hlogm_pos
            linarith
          have hmul : Real.log 4 * (1 / Real.log (2 : ℝ) - 1 / Real.log (m : ℝ)) ≤
              Real.log 4 * (1 / Real.log (2 : ℝ)) := mul_le_mul_of_nonneg_left this hlog4_nn
          have hdiv : Real.log 4 * (1 / Real.log (2 : ℝ)) = Real.log 4 / Real.log 2 := by ring
          norm_num at *
          linarith
  have hloglog2 : -1 ≤ Real.log (Real.log 2) := by
    have h1 : Real.exp (-1) ≤ Real.log 2 := by
      have h2 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 1 / 2)]
        have := Real.add_one_le_exp (1 : ℝ); linarith
      linarith
    have h3 : Real.log (Real.exp (-1)) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (Real.exp_pos (-1)) h1
    rwa [Real.log_exp] at h3
  have hratio : Real.log 4 / Real.log 2 = 2 := by
    rw [hlog4_eq]; field_simp [ne_of_gt (by linarith : (0 : ℝ) < Real.log 2)]
  linarith

lemma sum_inv_sq_le_one (m : ℕ) :
    ∑ k ∈ Finset.Icc 2 m, (1 : ℝ) / ((k : ℝ) ^ 2) ≤ 1 := by
  have hstep : ∀ k ∈ Finset.Icc 2 m,
      (1 : ℝ) / ((k : ℝ) ^ 2) ≤ 1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have h1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
    have h2 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    have hdiff : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) = 1 / (((k : ℝ) - 1) * (k : ℝ)) := by
      field_simp [ne_of_gt (by linarith : (0 : ℝ) < (k : ℝ) - 1), ne_of_gt h2]; ring
    rw [hdiff]
    apply one_div_le_one_div_of_le (mul_pos (by linarith) h2)
    nlinarith
  calc ∑ k ∈ Finset.Icc 2 m, (1 : ℝ) / ((k : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.Icc 2 m, (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) := Finset.sum_le_sum hstep
    _ ≤ 1 := by
      induction m with
      | zero => simp
      | succ m ih =>
        by_cases hm : m < 1
        · have : Finset.Icc 2 (m + 1) = ∅ := by ext x; simp; omega
          rw [this, Finset.sum_empty]; norm_num
        · by_cases hm1 : m = 1
          · subst hm1; norm_num
          · have htele : ∀ b ≥ 2, ∑ k ∈ Finset.Icc 2 b, (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) =
                1 - 1 / (b : ℝ) := by
              intro b hb
              induction b with
              | zero => omega
              | succ b ihb =>
                by_cases hb1 : b = 1
                · subst hb1; norm_num
                · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ b + 1), ihb (by omega)]
                  have hsub : b + 1 - 1 = b := by omega
                  rw [hsub]; ring
            rw [htele (m + 1) (by omega)]
            have : (0 : ℝ) < 1 / ((m + 1 : ℕ) : ℝ) := by positivity
            linarith

lemma one_sub_ge_exp_neg_sub_two_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-t - 2 * t ^ 2) ≤ 1 - t := by
  have hpos : 0 < 1 - t := by linarith
  have h1 : Real.log (1 / (1 - t)) ≤ 1 / (1 - t) - 1 := Real.log_le_sub_one_of_pos (one_div_pos.mpr hpos)
  rw [one_div, Real.log_inv] at h1
  have h2 : (1 - t)⁻¹ - 1 ≤ t + 2 * t ^ 2 := by
    have hdiff : (1 - t)⁻¹ - 1 = t / (1 - t) := by field_simp [ne_of_gt hpos]; ring
    rw [hdiff, div_le_iff₀ hpos]
    nlinarith [sq_nonneg t]
  have h3 : -t - 2 * t ^ 2 ≤ Real.log (1 - t) := by linarith
  calc Real.exp (-t - 2 * t ^ 2) ≤ Real.exp (Real.log (1 - t)) := Real.exp_le_exp.mpr h3
    _ = 1 - t := Real.exp_log hpos

/-- Mertens product lower bound: `∏_{p ≤ m} (1 - 1/p) ≥ exp (-8) / log m` for `m ≥ 3`. -/
lemma prod_one_sub_inv_ge {m : ℕ} (hm : 3 ≤ m) :
    Real.exp (-8) / Real.log (m : ℝ) ≤
      ∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) := by
  have hstep : ∀ p ∈ (Finset.Icc 2 m).filter Nat.Prime,
      Real.exp (-(1 : ℝ) / (p : ℝ) - 2 * ((1 : ℝ) / ((p : ℝ) ^ 2))) ≤ 1 - (1 : ℝ) / (p : ℝ) := by
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have ht1 : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)
    have h := one_sub_ge_exp_neg_sub_two_sq (t := (1 : ℝ) / (p : ℝ)) (by positivity) ht1
    convert h using 2; ring
  have hprod : Real.exp (∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime,
      (-(1 : ℝ) / (p : ℝ) - 2 * ((1 : ℝ) / ((p : ℝ) ^ 2)))) ≤
      ∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) := by
    rw [Real.exp_sum]
    exact real_prod_le_prod (fun _ _ => le_of_lt (Real.exp_pos _)) hstep
  have hsum_eq : ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime,
      (-(1 : ℝ) / (p : ℝ) - 2 * ((1 : ℝ) / ((p : ℝ) ^ 2))) =
      -(∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
      2 * (∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) ^ 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  have h1 := sum_inv_primes_le_log_log hm
  have h2 : ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) ^ 2) ≤ 1 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity))
      (sum_inv_sq_le_one m)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hexp_eq : Real.exp (-8 - Real.log (Real.log (m : ℝ))) = Real.exp (-8) / Real.log (m : ℝ) := by
    rw [Real.exp_sub, Real.exp_log hlogm_pos]
  rw [← hexp_eq]
  exact le_trans (Real.exp_le_exp.mpr (by linarith)) hprod

/-- Lower bound on `∏_{3 ≤ p ≤ m} (1 - 2/p)` via `∏_{p ≤ m} (1 - 1/p)^2`. -/
lemma prod_one_sub_two_div_ge {m : ℕ} (hm : 3 ≤ m) :
    Real.exp (-18) / (Real.log (m : ℝ)) ^ 2 ≤
      ∏ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 - (2 : ℝ) / (p : ℝ)) := by
  have h1 : ∀ p ∈ (Finset.Icc 3 m).filter Nat.Prime,
      (1 - (1 : ℝ) / (p : ℝ)) ^ 2 * Real.exp (-2 / ((p - 1 : ℕ) : ℝ) ^ 2) ≤ 1 - (2 : ℝ) / (p : ℝ) := by
    intro p hp
    have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
    have hpm1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    have hratio : 1 - (2 : ℝ) / (p : ℝ) =
        (1 - (1 : ℝ) / (p : ℝ)) ^ 2 * (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2) := by
      rw [hcast]; field_simp [ne_of_gt hp_pos, ne_of_gt hpm1_pos]; ring
    rw [hratio]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have ht_le : (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
      have hge2 : (2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ p - 1)
      have hge4 : (4 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      exact one_div_le_one_div_of_le (by norm_num) hge4
    have hstep := one_sub_ge_exp_neg_sub_two_sq (t := 1 / ((p - 1 : ℕ) : ℝ) ^ 2) (by positivity) (by linarith)
    refine le_trans (Real.exp_le_exp.mpr ?_) hstep
    have ht_nn : (0 : ℝ) ≤ 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hsq_le : 2 * (1 / ((p - 1 : ℕ) : ℝ) ^ 2) ^ 2 ≤ 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have hrew : -2 / ((p - 1 : ℕ) : ℝ) ^ 2 = -2 * (1 / ((p - 1 : ℕ) : ℝ) ^ 2) := by ring
    linarith
  have hprod1 : (∏ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) ^ 2) *
      Real.exp (∑ p ∈ (Finset.Icc 3 m).filter Nat.Prime, -2 / ((p - 1 : ℕ) : ℝ) ^ 2) ≤
      ∏ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 - (2 : ℝ) / (p : ℝ)) := by
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    exact real_prod_le_prod (fun _ _ => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))) h1
  have hsum_err : -2 ≤ ∑ p ∈ (Finset.Icc 3 m).filter Nat.Prime, -2 / ((p - 1 : ℕ) : ℝ) ^ 2 := by
    have hsub : ((Finset.Icc 3 m).filter Nat.Prime).image (fun p : ℕ => p - 1) ⊆ Finset.Icc 2 m := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
      have hpI := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hinj : Set.InjOn (fun p : ℕ => p - 1) ((Finset.Icc 3 m).filter Nat.Prime : Set ℕ) := by
      intro a ha b hb hab
      have ha3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      have hb3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
      dsimp only at hab
      omega
    have hpos_sum : ∑ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
      have heq : ∑ x ∈ ((Finset.Icc 3 m).filter Nat.Prime).image (fun p : ℕ => p - 1), (1 : ℝ) / (x : ℝ) ^ 2 =
          ∑ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2 :=
        Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)
      rw [← heq]
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
        (sum_inv_sq_le_one m)
    have hmul : ∑ p ∈ (Finset.Icc 3 m).filter Nat.Prime, -2 / ((p - 1 : ℕ) : ℝ) ^ 2 =
        -2 * ∑ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    linarith
  have hprod2 : ∏ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) =
      (1 / 2 : ℝ) * ∏ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) := by
    have hsplit : (Finset.Icc 2 m).filter Nat.Prime =
        insert 2 ((Finset.Icc 3 m).filter Nat.Prime) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
      constructor
      · intro ⟨⟨h1, h2⟩, hp⟩
        by_cases hp2 : p = 2
        · left; exact hp2
        · right; exact ⟨⟨by omega, h2⟩, hp⟩
      · rintro (rfl | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨⟨by omega, by omega⟩, Nat.prime_two⟩
        · exact ⟨⟨by omega, h2⟩, hp⟩
    rw [hsplit, Finset.prod_insert (by simp)]
    norm_num
  have hbase := prod_one_sub_inv_ge hm
  rw [hprod2] at hbase
  have hprod3_ge : Real.exp (-8) / Real.log (m : ℝ) ≤
      ∏ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) := by
    have hnn : 0 ≤ ∏ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) :=
      Finset.prod_nonneg (fun p hp => by
        have hp3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        have : (1 : ℝ) / (p : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (by omega : 0 < p))]; exact_mod_cast (by omega : 1 ≤ p)
        linarith)
    linarith
  have hsq_ge : (Real.exp (-8) / Real.log (m : ℝ)) ^ 2 ≤
      ∏ p ∈ (Finset.Icc 3 m).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) ^ 2 := by
    rw [Finset.prod_pow]
    exact pow_le_pow_left₀ (by positivity) hprod3_ge 2
  have hexp_ge : Real.exp (-2) ≤
      Real.exp (∑ p ∈ (Finset.Icc 3 m).filter Nat.Prime, -2 / ((p - 1 : ℕ) : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr hsum_err
  have hfinal : (Real.exp (-8) / Real.log (m : ℝ)) ^ 2 * Real.exp (-2) =
      Real.exp (-18) / (Real.log (m : ℝ)) ^ 2 := by
    rw [div_pow, ← Real.exp_nat_mul]
    have : Real.exp ((2 : ℕ) * (-8 : ℝ)) * Real.exp (-2) = Real.exp (-18) := by
      rw [← Real.exp_add]; norm_num
    rw [div_mul_eq_mul_div, this]
  rw [← hfinal]
  exact le_trans (mul_le_mul hsq_ge hexp_ge (le_of_lt (Real.exp_pos _)) (Finset.prod_nonneg (fun _ _ => sq_nonneg _)))
    hprod1

/-!
## Part 3: Lower bound on `x4 n` in terms of `(n / n.totient) * n / (log n)^2`
-/

lemma totient_div_eq_prod (n : ℕ) (hn : 0 < n) :
    (n.totient : ℝ) / (n : ℝ) = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  have h := Nat.totient_eq_mul_prod_factors n
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hcast : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
    have hq := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at hq
    simpa [one_div] using hq
  rw [hcast, mul_div_cancel_left₀ _ hn_ne]

lemma card_primeFactors_gt_sqrt_le_one (n : ℕ) (hn : 1 ≤ n) :
    (n.primeFactors.filter (fun p => Nat.sqrt n < p)).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  have hpP : Nat.Prime p := (Nat.mem_primeFactors.mp hp'.1).1
  have hqP : Nat.Prime q := (Nat.mem_primeFactors.mp hq'.1).1
  have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp'.1).2.1
  have hqdvd : q ∣ n := (Nat.mem_primeFactors.mp hq'.1).2.1
  have hmul_dvd : p * q ∣ n := (Nat.coprime_primes hpP hqP |>.mpr hpq).mul_dvd_of_dvd_of_dvd hpdvd hqdvd
  have hmul_le : p * q ≤ n := Nat.le_of_dvd (by omega) hmul_dvd
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have hge : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ p * q := Nat.mul_le_mul hp'.2 hq'.2
  omega

lemma sieve_prod_lower_bound {n : ℕ} (hn : 100 ≤ n) (heven : Even n) :
    (1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) *
      (∏ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime, (1 - (2 : ℝ) / (p : ℝ))) ≤
    ((n.totient : ℝ) / (n : ℝ)) *
      (∏ p ∈ ((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime).filter (fun p => ¬ p ∣ n),
        (1 - (2 : ℝ) / (p : ℝ))) := by
  have hn_pos : 0 < n := by omega
  have htot_pos : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn_pos
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp heven
  have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, by omega⟩
  have hsqrt_ge : 10 ≤ Nat.sqrt n := by
    have : 10 ^ 2 ≤ n := by omega
    exact Nat.le_sqrt.mpr (by omega)
  -- Partition `n.primeFactors` into `{2}`, `A = {3 ≤ p ≤ √n}`, `B = {√n < p}`
  let A := n.primeFactors.filter (fun p => 3 ≤ p ∧ p ≤ Nat.sqrt n)
  let B := n.primeFactors.filter (fun p => Nat.sqrt n < p)
  have hpf_eq : n.primeFactors = insert 2 (A ∪ B) := by
    ext p
    simp only [A, B, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      have hp2 := (Nat.mem_primeFactors.mp hp).1.two_le
      by_cases h2 : p = 2
      · left; exact h2
      · right
        by_cases hle : p ≤ Nat.sqrt n
        · left; exact ⟨hp, by omega, hle⟩
        · right; exact ⟨hp, by omega⟩
    · rintro (rfl | ⟨hp, _⟩ | ⟨hp, _⟩)
      · exact h2mem
      · exact hp
      · exact hp
  have h2notAB : 2 ∉ A ∪ B := by
    simp only [A, B, Finset.mem_union, Finset.mem_filter]; omega
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2.2
    have h2 := (Finset.mem_filter.mp hp2).2
    omega
  -- Split `primes(3..√n)` into `A` and `C = primes(2..√n) with ¬p ∣ n`
  let C := ((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime).filter (fun p => ¬ p ∣ n)
  have hAC_eq : (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime = A ∪ C := by
    ext p
    simp only [A, C, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
    constructor
    · intro ⟨⟨h1, h2⟩, hp⟩
      by_cases hd : p ∣ n
      · left; exact ⟨⟨hp, hd, by omega⟩, h1, h2⟩
      · right; exact ⟨⟨⟨by omega, h2⟩, hp⟩, hd⟩
    · rintro (⟨⟨hp, _, _⟩, h1, h2⟩ | ⟨⟨⟨h1, h2⟩, hp⟩, hnd⟩)
      · exact ⟨⟨h1, h2⟩, hp⟩
      · have hpne2 : p ≠ 2 := fun heq => hnd (heq ▸ h2dvd)
        exact ⟨⟨by omega, h2⟩, hp⟩
  have hdisjAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have hd := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp1).1).2.1
    have hnd := (Finset.mem_filter.mp hp2).2
    exact hnd hd
  -- Rewrite totient ratio
  have htot := totient_div_eq_prod n hn_pos
  rw [htot]
  -- Evaluate `n / n.totient` as inverse of product
  have hinv_tot : (n : ℝ) / (n.totient : ℝ) = (∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ := by
    rw [← htot, inv_div]
  rw [hinv_tot, hpf_eq, Finset.prod_insert h2notAB, Finset.prod_union hdisjAB,
    hAC_eq, Finset.prod_union hdisjAC]
  have h2val : (1 - (1 : ℝ) / ((2 : ℕ) : ℝ)) = 1 / 2 := by norm_num
  rw [h2val]
  -- Positivity of products
  have hA_pos : 0 < ∏ p ∈ A, (1 - (1 : ℝ) / (p : ℝ)) :=
    Finset.prod_pos (fun p hp => by
      have hp3 := (Finset.mem_filter.mp hp).2.1
      have : (1 : ℝ) / (p : ℝ) < 1 := by
        rw [div_lt_one (by exact_mod_cast (by omega : 0 < p))]; exact_mod_cast (by omega : 1 < p)
      linarith)
  have hB_pos : 0 < ∏ p ∈ B, (1 - (1 : ℝ) / (p : ℝ)) :=
    Finset.prod_pos (fun p hp => by
      have hp2 := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.two_le
      have : (1 : ℝ) / (p : ℝ) < 1 := by
        rw [div_lt_one (by exact_mod_cast (by omega : 0 < p))]; exact_mod_cast (by omega : 1 < p)
      linarith)
  have hC_nn : 0 ≤ ∏ p ∈ C, (1 - (2 : ℝ) / (p : ℝ)) :=
    Finset.prod_nonneg (fun p hp => by
      have hp2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.two_le
      have hnd := (Finset.mem_filter.mp hp).2
      have hpne2 : p ≠ 2 := fun heq => hnd (heq ▸ h2dvd)
      have : (2 : ℝ) / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (by omega : 0 < p))]; exact_mod_cast (by omega : 2 ≤ p)
      linarith)
  -- `∏_{p ∈ B} (1 - 1/p) ≥ 3/4`
  have hB_ge' : (3 / 4 : ℝ) ≤ ∏ p ∈ B, (1 - (1 : ℝ) / (p : ℝ)) := by
    have hcard : B.card ≤ 1 := card_primeFactors_gt_sqrt_le_one n (by omega)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty]; norm_num
    · rcases Finset.card_eq_one.mp h1 with ⟨p, hpB⟩
      rw [hpB, Finset.prod_singleton]
      have hp_mem : p ∈ B := hpB ▸ Finset.mem_singleton_self p
      have hpgt : Nat.sqrt n < p := (Finset.mem_filter.mp hp_mem).2
      have hp4 : 4 ≤ p := by omega
      have : (1 : ℝ) / (p : ℝ) ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp4)
      linarith
  -- For `p ∈ A`, `(1 - 2/p) ≤ (1 - 1/p)^2`
  have hA_cmp : ∏ p ∈ A, (1 - (2 : ℝ) / (p : ℝ)) ≤
      (∏ p ∈ A, (1 - (1 : ℝ) / (p : ℝ))) ^ 2 := by
    rw [← Finset.prod_pow]
    apply real_prod_le_prod
    · intro p hp
      have hp3 := (Finset.mem_filter.mp hp).2.1
      have : (2 : ℝ) / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (by omega : 0 < p))]; exact_mod_cast (by omega : 2 ≤ p)
      linarith
    · intro p _
      have : (1 - (1 : ℝ) / (p : ℝ)) ^ 2 = 1 - 2 / (p : ℝ) + (1 / (p : ℝ)) ^ 2 := by ring
      nlinarith [sq_nonneg ((1 : ℝ) / (p : ℝ))]
  set PA := ∏ p ∈ A, (1 - (1 : ℝ) / (p : ℝ))
  set PB := ∏ p ∈ B, (1 - (1 : ℝ) / (p : ℝ))
  set PA2 := ∏ p ∈ A, (1 - (2 : ℝ) / (p : ℝ))
  set PC := ∏ p ∈ C, (1 - (2 : ℝ) / (p : ℝ))
  have hcore : (1 / 8 : ℝ) * (1 / 2 * (PA * PB))⁻¹ * PA2 ≤ 1 / 2 * (PA * PB) := by
    have hden_pos : 0 < 1 / 2 * (PA * PB) := by positivity
    rw [mul_assoc, inv_mul_eq_div, mul_div_assoc', div_le_iff₀ hden_pos]
    have hPB2 : (9 / 16 : ℝ) ≤ PB ^ 2 := by nlinarith
    have hPA2_le : PA2 ≤ PA ^ 2 := hA_cmp
    have h1 : (1 / 8 : ℝ) * PA2 ≤ (1 / 8 : ℝ) * PA ^ 2 := by linarith
    have h2 : (1 / 8 : ℝ) * PA ^ 2 ≤ (1 / 4 : ℝ) * PA ^ 2 * PB ^ 2 := by
      have : (1 / 8 : ℝ) ≤ (1 / 4 : ℝ) * PB ^ 2 := by linarith
      nlinarith [sq_nonneg PA]
    nlinarith
  calc (1 / 8 : ℝ) * (1 / 2 * (PA * PB))⁻¹ * (PA2 * PC)
      = ((1 / 8 : ℝ) * (1 / 2 * (PA * PB))⁻¹ * PA2) * PC := by ring
    _ ≤ (1 / 2 * (PA * PB)) * PC := mul_le_mul_of_nonneg_right hcore hC_nn

/-!
## Part 4: Elementary Selberg Upper-Bound Sieve
-/

/-- Number of forbidden residue classes mod `d` for `q * (n - p * q) ≡ 0 (mod d)`. -/
def omega (n d : ℕ) : ℕ :=
  ∏ r ∈ d.primeFactors.filter (fun r => ¬ r ∣ n), (2 : ℕ)

lemma omega_pos (n d : ℕ) : 0 < omega n d := by
  unfold omega
  exact Finset.prod_pos (fun _ _ => by norm_num)

lemma omega_one (n : ℕ) : omega n 1 = 1 := by
  simp [omega]

lemma omega_prime (n r : ℕ) (hr : Nat.Prime r) :
    omega n r = if r ∣ n then 1 else 2 := by
  unfold omega
  rw [hr.primeFactors]
  by_cases h : r ∣ n
  · rw [if_pos h, Finset.filter_singleton, if_neg (not_not.mpr h), Finset.prod_empty]
  · rw [if_neg h, Finset.filter_singleton, if_pos h, Finset.prod_singleton]

lemma omega_mul_of_coprime {n a b : ℕ} (hcop : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    omega n (a * b) = omega n a * omega n b := by
  unfold omega
  rw [Nat.primeFactors_mul ha hb, Finset.filter_union, Finset.prod_union]
  rw [Finset.disjoint_left]
  intro r hr1 hr2
  have h1 := Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr1).1
  have h2 := Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr2).1
  have hdvd : r ∣ Nat.gcd a b := Nat.dvd_gcd h1.2.1 h2.2.1
  rw [hcop.gcd_eq_one] at hdvd
  exact h1.1.not_dvd_one hdvd

lemma omega_le_self {n d : ℕ} (hd : Squarefree d) (heven : Even n) : omega n d ≤ d := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hprod : ∏ r ∈ d.primeFactors, r = d := Nat.prod_primeFactors_of_squarefree hd
  calc omega n d
      = ∏ r ∈ d.primeFactors.filter (fun r => ¬ r ∣ n), (2 : ℕ) := rfl
    _ ≤ ∏ r ∈ d.primeFactors.filter (fun r => ¬ r ∣ n), r :=
        Finset.prod_le_prod' (fun r hr => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr).1).1.two_le)
    _ ≤ ∏ r ∈ d.primeFactors, r :=
        Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
          (fun r hr _ => (Nat.mem_primeFactors.mp hr).1.one_le)
    _ = d := hprod

/-- For prime `r` not dividing `p`, count of `x ∈ range r` with `r ∣ x * (n - p * x)` in `ℤ` is `omega n r`. -/
lemma card_roots_prime {n p r : ℕ} (hr : Nat.Prime r) (hp_cop : Nat.Coprime p r) :
    ((Finset.range r).filter (fun x : ℕ => (r : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)))).card =
      omega n r := by
  rw [omega_prime n r hr]
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hrn : r ∣ n
  · rw [if_pos hrn]
    have heq : (Finset.range r).filter (fun x : ℕ => (r : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ))) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · intro ⟨hx, hdvd⟩
        have hrZ : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
        rcases hrZ.dvd_or_dvd hdvd with h1 | h2
        · have h1' : r ∣ x := Int.natCast_dvd_natCast.mp h1
          exact Nat.eq_zero_of_dvd_of_lt h1' hx
        · have hrnZ : (r : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hrn
          have hpx : (r : ℤ) ∣ (p : ℤ) * (x : ℤ) := by
            have := dvd_sub hrnZ h2; simpa using this
          rcases hrZ.dvd_or_dvd hpx with hp' | hx'
          · exfalso
            have hp_dvd : r ∣ p := Int.natCast_dvd_natCast.mp hp'
            have := Nat.dvd_gcd hp_dvd dvd_rfl
            rw [hp_cop.gcd_eq_one] at this
            exact hr.not_dvd_one this
          · exact Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd_natCast.mp hx') hx
      · rintro rfl
        exact ⟨hr.pos, by simp⟩
    rw [heq, Finset.card_singleton]
  · rw [if_neg hrn]
    have hp_ne : (p : ZMod r) ≠ 0 := by
      intro h
      have hp_dvd : r ∣ p := (ZMod.natCast_eq_zero_iff p r).mp h
      have := Nat.dvd_gcd hp_dvd dvd_rfl
      rw [hp_cop.gcd_eq_one] at this
      exact hr.not_dvd_one this
    have hn_ne : (n : ZMod r) ≠ 0 := by
      intro h; exact hrn ((ZMod.natCast_eq_zero_iff n r).mp h)
    let x0 : ℕ := ((n : ZMod r) * (p : ZMod r)⁻¹).val
    have hx0_lt : x0 < r := ZMod.val_lt _
    have hx0_ne0 : x0 ≠ 0 := by
      intro h
      have h0 : ((n : ZMod r) * (p : ZMod r)⁻¹) = 0 := by
        have := ZMod.natCast_zmod_val ((n : ZMod r) * (p : ZMod r)⁻¹)
        rw [← this]; simp [x0, h]
      rcases mul_eq_zero.mp h0 with h1 | h2
      · exact hn_ne h1
      · exact inv_ne_zero hp_ne h2
    have heq : (Finset.range r).filter (fun x : ℕ => (r : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ))) = {0, x0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hx, hdvd⟩
        have hz : (((x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)) : ℤ) : ZMod r) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hdvd
        push_cast at hz
        rcases mul_eq_zero.mp hz with h1 | h2
        · left
          have : r ∣ x := (ZMod.natCast_eq_zero_iff x r).mp h1
          exact Nat.eq_zero_of_dvd_of_lt this hx
        · right
          have hpx : (p : ZMod r) * (x : ZMod r) = (n : ZMod r) := by linear_combination -h2
          have hxz : (x : ZMod r) = (n : ZMod r) * (p : ZMod r)⁻¹ := by
            calc (x : ZMod r) = (p : ZMod r)⁻¹ * ((p : ZMod r) * (x : ZMod r)) := by
                  rw [← mul_assoc, inv_mul_cancel₀ hp_ne, one_mul]
              _ = (p : ZMod r)⁻¹ * (n : ZMod r) := by rw [hpx]
              _ = (n : ZMod r) * (p : ZMod r)⁻¹ := mul_comm _ _
          have hval := congrArg ZMod.val hxz
          rwa [ZMod.val_natCast_of_lt hx] at hval
      · rintro (rfl | rfl)
        · exact ⟨hr.pos, by simp⟩
        · refine ⟨hx0_lt, ?_⟩
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          have hcast : (x0 : ZMod r) = (n : ZMod r) * (p : ZMod r)⁻¹ := ZMod.natCast_zmod_val _
          rw [hcast]
          have : (p : ZMod r) * ((n : ZMod r) * (p : ZMod r)⁻¹) = (n : ZMod r) := by
            rw [mul_comm (n : ZMod r), ← mul_assoc, mul_inv_cancel₀ hp_ne, one_mul]
          rw [this, sub_self, mul_zero]
    rw [heq, Finset.card_pair hx0_ne0.symm]

/-- By CRT, for squarefree `d` coprime to `p`, the number of roots mod `d` is `omega n d`. -/
lemma card_roots_squarefree {n p d : ℕ} (hd : Squarefree d) (hp_cop : Nat.Coprime p d) :
    ((Finset.range d).filter (fun x : ℕ => (d : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)))).card =
      omega n d := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases hd1 : d = 1
    · subst hd1; simp [omega_one]
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
      let r := d.minFac
      have hr : Nat.Prime r := Nat.minFac_prime hd1
      have hrdvd : r ∣ d := Nat.minFac_dvd d
      let d' := d / r
      have hd_eq : d = r * d' := (Nat.mul_div_cancel' hrdvd).symm
      have hd'_sf : Squarefree d' := by
        rw [hd_eq] at hd; exact hd.of_mul_right
      have hcop_rd' : Nat.Coprime r d' := by
        refine hr.coprime_iff_not_dvd.mpr ?_
        intro h
        rw [hd_eq] at hd
        exact hr.ne_one (isUnit_iff_eq_one.mp (hd r (Nat.mul_dvd_mul_left r h)))
      have hp_r : Nat.Coprime p r := (Nat.coprime_mul_iff_right.mp (hd_eq ▸ hp_cop)).1
      have hp_d' : Nat.Coprime p d' := (Nat.coprime_mul_iff_right.mp (hd_eq ▸ hp_cop)).2
      have hd'_lt : d' < d := Nat.div_lt_self hd_pos hr.one_lt
      have ih_d' := ih d' hd'_lt hd'_sf hp_d'
      have h_r := card_roots_prime (n := n) hr hp_r
      -- Bijection between roots mod `r * d'` and `(roots mod r) × (roots mod d')` via CRT
      let S_d := (Finset.range d).filter (fun x : ℕ => (d : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)))
      let S_r := (Finset.range r).filter (fun x : ℕ => (r : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)))
      let S_d' := (Finset.range d').filter (fun x : ℕ => (d' : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)))
      have hbij : S_d.card = (S_r ×ˢ S_d').card := by
        apply Finset.card_bij (fun x _ => (x % r, x % d'))
        · intro x hx
          have hx' := Finset.mem_filter.mp hx
          have hdvd_d := hx'.2
          rw [Finset.mem_product]
          constructor
          · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt x hr.pos), ?_⟩
            have hdvd_r : (r : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)) :=
              dvd_trans (Int.natCast_dvd_natCast.mpr hrdvd) hdvd_d
            have hmod : (r : ℤ) ∣ (x : ℤ) - ((x % r : ℕ) : ℤ) := by
              have := Int.emod_add_mul_ediv (x : ℤ) (r : ℤ)
              refine ⟨(x : ℤ) / (r : ℤ), ?_⟩
              have hcast : ((x % r : ℕ) : ℤ) = (x : ℤ) % (r : ℤ) := by simp
              linarith
            have hpoly : (r : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)) -
                ((x % r : ℕ) : ℤ) * ((n : ℤ) - (p : ℤ) * ((x % r : ℕ) : ℤ)) := by
              have hfac : (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)) -
                  ((x % r : ℕ) : ℤ) * ((n : ℤ) - (p : ℤ) * ((x % r : ℕ) : ℤ)) =
                  ((x : ℤ) - ((x % r : ℕ) : ℤ)) * ((n : ℤ) - (p : ℤ) * ((x : ℤ) + ((x % r : ℕ) : ℤ))) := by ring
              rw [hfac]; exact dvd_mul_of_dvd_left hmod _
            have := dvd_sub hdvd_r hpoly; simpa using this
          · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt x (Nat.pos_of_ne_zero hd'_sf.ne_zero)), ?_⟩
            have hd'dvd : d' ∣ d := hd_eq ▸ dvd_mul_left d' r
            have hdvd_d' : (d' : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)) :=
              dvd_trans (Int.natCast_dvd_natCast.mpr hd'dvd) hdvd_d
            have hmod : (d' : ℤ) ∣ (x : ℤ) - ((x % d' : ℕ) : ℤ) := by
              have := Int.emod_add_mul_ediv (x : ℤ) (d' : ℤ)
              refine ⟨(x : ℤ) / (d' : ℤ), ?_⟩
              have hcast : ((x % d' : ℕ) : ℤ) = (x : ℤ) % (d' : ℤ) := by simp
              linarith
            have hpoly : (d' : ℤ) ∣ (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)) -
                ((x % d' : ℕ) : ℤ) * ((n : ℤ) - (p : ℤ) * ((x % d' : ℕ) : ℤ)) := by
              have hfac : (x : ℤ) * ((n : ℤ) - (p : ℤ) * (x : ℤ)) -
                  ((x % d' : ℕ) : ℤ) * ((n : ℤ) - (p : ℤ) * ((x % d' : ℕ) : ℤ)) =
                  ((x : ℤ) - ((x % d' : ℕ) : ℤ)) * ((n : ℤ) - (p : ℤ) * ((x : ℤ) + ((x % d' : ℕ) : ℤ))) := by ring
              rw [hfac]; exact dvd_mul_of_dvd_left hmod _
            have := dvd_sub hdvd_d' hpoly; simpa using this
        · intro a ha b hb hab
          have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
          have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
          have h1 : a ≡ b [MOD r] := congrArg Prod.fst hab
          have h2 : a ≡ b [MOD d'] := congrArg Prod.snd hab
          have h3 : a ≡ b [MOD r * d'] := (Nat.modEq_and_modEq_iff_modEq_mul hcop_rd').mp ⟨h1, h2⟩
          rw [← hd_eq] at h3
          rw [Nat.ModEq, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h3
          exact h3
        · intro ⟨u, v⟩ huv
          rw [Finset.mem_product] at huv
          have hu := Finset.mem_filter.mp huv.1
          have hv := Finset.mem_filter.mp huv.2
          let c := Nat.chineseRemainder hcop_rd' u v
          let x0 : ℕ := c.1 % d
          have hx_lt : x0 < d := Nat.mod_lt _ hd_pos
          have hx_r : x0 % r = u := by
            have hmod : x0 ≡ c.1 [MOD r] := (Nat.mod_modEq c.1 d).of_dvd hrdvd
            have h1 : c.1 ≡ u [MOD r] := c.2.1
            have h2 := hmod.trans h1
            rwa [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.mp hu.1)] at h2
          have hx_d' : x0 % d' = v := by
            have hd'dvd : d' ∣ d := hd_eq ▸ dvd_mul_left d' r
            have hmod : x0 ≡ c.1 [MOD d'] := (Nat.mod_modEq c.1 d).of_dvd hd'dvd
            have h1 : c.1 ≡ v [MOD d'] := c.2.2
            have h2 := hmod.trans h1
            rwa [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.mp hv.1)] at h2
          refine ⟨x0, ?_, Prod.ext hx_r hx_d'⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx_lt, ?_⟩
          have hdvd_r : (r : ℤ) ∣ (x0 : ℤ) * ((n : ℤ) - (p : ℤ) * (x0 : ℤ)) := by
            have hmod : (r : ℤ) ∣ (x0 : ℤ) - (u : ℤ) := by
              rw [← hx_r]
              have := Int.emod_add_mul_ediv (x0 : ℤ) (r : ℤ)
              refine ⟨(x0 : ℤ) / (r : ℤ), ?_⟩
              have hcast : ((x0 % r : ℕ) : ℤ) = (x0 : ℤ) % (r : ℤ) := by simp
              linarith
            have hpoly : (r : ℤ) ∣ (x0 : ℤ) * ((n : ℤ) - (p : ℤ) * (x0 : ℤ)) -
                (u : ℤ) * ((n : ℤ) - (p : ℤ) * (u : ℤ)) := by
              have hfac : (x0 : ℤ) * ((n : ℤ) - (p : ℤ) * (x0 : ℤ)) -
                  (u : ℤ) * ((n : ℤ) - (p : ℤ) * (u : ℤ)) =
                  ((x0 : ℤ) - (u : ℤ)) * ((n : ℤ) - (p : ℤ) * ((x0 : ℤ) + (u : ℤ))) := by ring
              rw [hfac]; exact dvd_mul_of_dvd_left hmod _
            have := dvd_add hu.2 hpoly; simpa using this
          have hdvd_d' : (d' : ℤ) ∣ (x0 : ℤ) * ((n : ℤ) - (p : ℤ) * (x0 : ℤ)) := by
            have hmod : (d' : ℤ) ∣ (x0 : ℤ) - (v : ℤ) := by
              rw [← hx_d']
              have := Int.emod_add_mul_ediv (x0 : ℤ) (d' : ℤ)
              refine ⟨(x0 : ℤ) / (d' : ℤ), ?_⟩
              have hcast : ((x0 % d' : ℕ) : ℤ) = (x0 : ℤ) % (d' : ℤ) := by simp
              linarith
            have hpoly : (d' : ℤ) ∣ (x0 : ℤ) * ((n : ℤ) - (p : ℤ) * (x0 : ℤ)) -
                (v : ℤ) * ((n : ℤ) - (p : ℤ) * (v : ℤ)) := by
              have hfac : (x0 : ℤ) * ((n : ℤ) - (p : ℤ) * (x0 : ℤ)) -
                  (v : ℤ) * ((n : ℤ) - (p : ℤ) * (v : ℤ)) =
                  ((x0 : ℤ) - (v : ℤ)) * ((n : ℤ) - (p : ℤ) * ((x0 : ℤ) + (v : ℤ))) := by ring
              rw [hfac]; exact dvd_mul_of_dvd_left hmod _
            have := dvd_add hv.2 hpoly; simpa using this
          have hcopZ : IsCoprime (r : ℤ) (d' : ℤ) := (Nat.isCoprime_iff_coprime).mpr hcop_rd'
          rw [hd_eq, Nat.cast_mul]
          exact hcopZ.mul_dvd hdvd_r hdvd_d'
      rw [hbij, Finset.card_product, h_r, ih_d', hd_eq,
        omega_mul_of_coprime hcop_rd' hr.ne_zero hd'_sf.ne_zero]

/-- Counting solutions in `Icc 1 X` to `d ∣ q * (n - p * q)` has error at most `omega n d`. -/
lemma card_Icc_dvd_quad_error {n p d X : ℕ} (hd : Squarefree d) (hp_cop : Nat.Coprime p d) :
    |(((Finset.Icc 1 X).filter (fun q : ℕ => (d : ℤ) ∣ (q : ℤ) * ((n : ℤ) - (p : ℤ) * (q : ℤ)))).card : ℝ) -
      ((omega n d : ℝ) / (d : ℝ)) * (X : ℝ)| ≤ (omega n d : ℝ) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  let P : ℕ → Prop := fun q => (d : ℤ) ∣ (q : ℤ) * ((n : ℤ) - (p : ℤ) * (q : ℤ))
  have hP_per : ∀ q, P (q + d) ↔ P q := by
    intro q
    dsimp only [P]
    have hdiff : ((q + d : ℕ) : ℤ) * ((n : ℤ) - (p : ℤ) * ((q + d : ℕ) : ℤ)) -
        (q : ℤ) * ((n : ℤ) - (p : ℤ) * (q : ℤ)) =
        (d : ℤ) * ((n : ℤ) - (p : ℤ) * (2 * (q : ℤ) + (d : ℤ))) := by push_cast; ring
    constructor
    · intro h
      have hsub := dvd_sub h (hdiff ▸ dvd_mul_right (d : ℤ) _)
      simpa using hsub
    · intro h
      have hadd := dvd_add h (hdiff ▸ dvd_mul_right (d : ℤ) _)
      simpa using hadd
  have hblock : ∀ a, ((Finset.Icc (a + 1) (a + d)).filter P).card = omega n d := by
    intro a
    rw [← card_roots_squarefree hd hp_cop]
    apply Finset.card_bij (fun q _ => q % d)
    · intro q hq
      have hq' := Finset.mem_filter.mp hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt q hd_pos), ?_⟩
      have hq_eq : q = q % d + d * (q / d) := (Nat.mod_add_div q d).symm
      have hiter : ∀ k x, P (x + d * k) ↔ P x := by
        intro k x
        induction k with
        | zero => simp
        | succ k ihk =>
          have : x + d * (k + 1) = (x + d * k) + d := by ring
          rw [this, hP_per, ihk]
      exact (hiter (q / d) (q % d)).mp (hq_eq ▸ hq'.2)
    · intro q1 hq1 q2 hq2 hmod
      have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hq1).1
      have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hq2).1
      have hme : q1 ≡ q2 [MOD d] := hmod
      by_cases hle : q1 ≤ q2
      · have hdvd : d ∣ q2 - q1 := (Nat.modEq_iff_dvd' hle).mp hme
        have hlt : q2 - q1 < d := by omega
        have h0 : q2 - q1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
        omega
      · have hle' : q2 ≤ q1 := by omega
        have hdvd : d ∣ q1 - q2 := (Nat.modEq_iff_dvd' hle').mp hme.symm
        have hlt : q1 - q2 < d := by omega
        have h0 : q1 - q2 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
        omega
    · intro r hr
      have hr' := Finset.mem_filter.mp hr
      have hr_lt := Finset.mem_range.mp hr'.1
      -- Unique `q ∈ [a+1, a+d]` with `q ≡ r [MOD d]`
      let q := a + 1 + ((r + d - (a + 1) % d) % d)
      have hq_mem : q ∈ Finset.Icc (a + 1) (a + d) := by
        refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
        have := Nat.mod_lt (r + d - (a + 1) % d) hd_pos
        omega
      have hq_mod : q % d = r := by
        have h1 : (a + 1) % d < d := Nat.mod_lt _ hd_pos
        have h2 : (a + 1 + (r + d - (a + 1) % d)) % d = r := by
          have hdiv := Nat.div_add_mod (a + 1) d
          have hmod_le : (a + 1) % d ≤ d := le_of_lt h1
          have : a + 1 + (r + d - (a + 1) % d) = d * ((a + 1) / d + 1) + r := by
            rw [mul_add, mul_one]; omega
          rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
        dsimp only [q]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h2]
      refine ⟨q, Finset.mem_filter.mpr ⟨hq_mem, ?_⟩, hq_mod⟩
      have hq_eq : q = r + d * (q / d) := by rw [← hq_mod]; exact (Nat.mod_add_div q d).symm
      have hiter : ∀ k x, P (x + d * k) ↔ P x := by
        intro k x
        induction k with
        | zero => simp
        | succ k ihk =>
          have : x + d * (k + 1) = (x + d * k) + d := by ring
          rw [this, hP_per, ihk]
      rw [hq_eq, hiter]
      exact hr'.2
  -- Partition `Icc 1 (k * d)` into `k` blocks of size `d`
  have hmult : ∀ k, ((Finset.Icc 1 (k * d)).filter P).card = k * omega n d := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      have hsplit : Finset.Icc 1 ((k + 1) * d) =
          Finset.Icc 1 (k * d) ∪ Finset.Icc (k * d + 1) (k * d + d) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_union]; ring_nf; omega
      have hdisj : Disjoint (Finset.Icc 1 (k * d)) (Finset.Icc (k * d + 1) (k * d + d)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_Icc] at hx1 hx2; omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
        ihk, hblock (k * d)]
      ring
  have hlo : (X / d) * omega n d ≤ ((Finset.Icc 1 X).filter P).card := by
    rw [← hmult (X / d)]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro x hx
    have hx' := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨hx'.1, le_trans hx'.2 (Nat.div_mul_le_self X d)⟩
  have hhi : ((Finset.Icc 1 X).filter P).card ≤ (X / d + 1) * omega n d := by
    rw [← hmult (X / d + 1)]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro x hx
    have hx' := Finset.mem_Icc.mp hx
    have hlt : X < d * (X / d + 1) := Nat.lt_mul_div_succ X hd_pos
    exact Finset.mem_Icc.mpr ⟨hx'.1, by nlinarith⟩
  have hloR : ((X / d : ℕ) : ℝ) * (omega n d : ℝ) ≤ (((Finset.Icc 1 X).filter P).card : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (((Finset.Icc 1 X).filter P).card : ℝ) ≤ (((X / d : ℕ) : ℝ) + 1) * (omega n d : ℝ) := by
    exact_mod_cast hhi
  have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hdiv1 : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_posR]; exact_mod_cast Nat.div_mul_le_self X d
  have hdiv2 : (X : ℝ) / (d : ℝ) < ((X / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hd_posR]
    have h1 : (X : ℝ) < (d : ℝ) * (((X / d : ℕ) : ℝ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ X hd_pos
    linarith
  have hom_nn : (0 : ℝ) ≤ (omega n d : ℝ) := by positivity
  rw [abs_le]
  have hrew : ((omega n d : ℝ) / (d : ℝ)) * (X : ℝ) = (X : ℝ) / (d : ℝ) * (omega n d : ℝ) := by ring
  constructor
  · rw [hrew]; nlinarith
  · rw [hrew]; nlinarith

/-- Multiplicative Selberg functions `f, g, h`. -/
noncomputable def fSel (n d : ℕ) : ℝ := (d : ℝ) / (omega n d : ℝ)

noncomputable def gSel (n d : ℕ) : ℝ :=
  ∏ r ∈ d.primeFactors, ((r : ℝ) - (omega n r : ℝ)) / (omega n r : ℝ)

noncomputable def hSel (n d : ℕ) : ℝ :=
  ∏ r ∈ d.primeFactors, (omega n r : ℝ) / ((r : ℝ) - (omega n r : ℝ))

lemma r_sub_omega_pos {n r : ℕ} (hr : Nat.Prime r) (heven : Even n) :
    (0 : ℝ) < (r : ℝ) - (omega n r : ℝ) := by
  rw [omega_prime n r hr]
  by_cases h : r ∣ n
  · rw [if_pos h]
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.two_le
    push_cast; linarith
  · rw [if_neg h]
    have hrne2 : r ≠ 2 := fun heq => h (heq ▸ even_iff_two_dvd.mp heven)
    have hr3 : 3 ≤ r := by have := hr.two_le; omega
    have : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
    push_cast; linarith

lemma gSel_pos {n d : ℕ} (heven : Even n) : 0 < gSel n d := by
  unfold gSel
  apply Finset.prod_pos
  intro r hr
  have hrP := (Nat.mem_primeFactors.mp hr).1
  exact div_pos (r_sub_omega_pos hrP heven) (by exact_mod_cast omega_pos n r)

lemma hSel_pos {n d : ℕ} (heven : Even n) : 0 < hSel n d := by
  unfold hSel
  apply Finset.prod_pos
  intro r hr
  have hrP := (Nat.mem_primeFactors.mp hr).1
  exact div_pos (by exact_mod_cast omega_pos n r) (r_sub_omega_pos hrP heven)

lemma gSel_mul_hSel {n d : ℕ} (heven : Even n) : gSel n d * hSel n d = 1 := by
  unfold gSel hSel
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro r hr
  have hrP := (Nat.mem_primeFactors.mp hr).1
  have h1 : (r : ℝ) - (omega n r : ℝ) ≠ 0 := ne_of_gt (r_sub_omega_pos hrP heven)
  have h2 : (omega n r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (omega_pos n r)
  field_simp [h1, h2]

lemma fSel_pos {n d : ℕ} (hd : 0 < d) : 0 < fSel n d :=
  div_pos (by exact_mod_cast hd) (by exact_mod_cast omega_pos n d)

lemma hSel_one (n : ℕ) : hSel n 1 = 1 := by simp [hSel]
lemma fSel_one (n : ℕ) : fSel n 1 = 1 := by simp [fSel, omega_one]

lemma hSel_mul_of_coprime {n a b : ℕ} (hcop : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    hSel n (a * b) = hSel n a * hSel n b := by
  unfold hSel
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union]
  rw [Finset.disjoint_left]
  intro r hr1 hr2
  have h1 := Nat.mem_primeFactors.mp hr1
  have h2 := Nat.mem_primeFactors.mp hr2
  have hdvd : r ∣ Nat.gcd a b := Nat.dvd_gcd h1.2.1 h2.2.1
  rw [hcop.gcd_eq_one] at hdvd
  exact h1.1.not_dvd_one hdvd

lemma fSel_mul_of_coprime {n a b : ℕ} (hcop : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    fSel n (a * b) = fSel n a * fSel n b := by
  unfold fSel
  rw [omega_mul_of_coprime hcop ha hb]
  push_cast; ring

lemma fSel_eq_prod_primeFactors {n x : ℕ} (hx : Squarefree x) :
    fSel n x = ∏ r ∈ x.primeFactors, (r : ℝ) / (omega n r : ℝ) := by
  unfold fSel
  have hpx : (x : ℝ) = ∏ r ∈ x.primeFactors, (r : ℝ) := by
    have h1 := (Nat.prod_primeFactors_of_squarefree hx).symm
    have h2 : (x : ℝ) = ((∏ r ∈ x.primeFactors, r : ℕ) : ℝ) := by exact_mod_cast h1
    rw [h2, Nat.cast_prod]
  have hom : (omega n x : ℝ) = ∏ r ∈ x.primeFactors, (omega n r : ℝ) := by
    unfold omega
    rw [Nat.cast_prod]
    have hsplit : x.primeFactors =
        x.primeFactors.filter (fun r => ¬ r ∣ n) ∪ x.primeFactors.filter (fun r => r ∣ n) := by
      ext r; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint (x.primeFactors.filter (fun r => ¬ r ∣ n))
        (x.primeFactors.filter (fun r => r ∣ n)) := by
      rw [Finset.disjoint_left]; intro r h1 h2
      exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    conv_rhs => rw [hsplit, Finset.prod_union hdisj]
    have h2 : ∏ r ∈ x.primeFactors.filter (fun r => r ∣ n),
        ((∏ q ∈ r.primeFactors.filter (fun q => ¬ q ∣ n), (2 : ℕ) : ℕ) : ℝ) = 1 := by
      apply Finset.prod_eq_one
      intro r hr
      have hrP := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr).1).1
      have h := omega_prime n r hrP
      unfold omega at h
      rw [h, if_pos (Finset.mem_filter.mp hr).2]; norm_num
    rw [h2, mul_one]
    apply Finset.prod_congr rfl
    intro r hr
    have hrP := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr).1).1
    have h := omega_prime n r hrP
    unfold omega at h
    rw [h, if_neg (Finset.mem_filter.mp hr).2]
  rw [hpx, hom, Finset.prod_div_distrib]

lemma squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpsq
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  have hne : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha0 hb0
  have hpow : p ^ 2 ∣ Nat.lcm a b := by simpa [sq] using hpsq
  have h2 : 2 ≤ (Nat.lcm a b).factorization p :=
    (hp.pow_dvd_iff_le_factorization hne).mp hpow
  rw [Nat.factorization_lcm ha0 hb0] at h2
  simp only [Finsupp.sup_apply] at h2
  rcases le_max_iff.mp h2 with h2a | h2b
  · exact hp.ne_one (isUnit_iff_eq_one.mp (ha p (by simpa [sq] using (hp.pow_dvd_iff_le_factorization ha0).mpr h2a)))
  · exact hp.ne_one (isUnit_iff_eq_one.mp (hb p (by simpa [sq] using (hp.pow_dvd_iff_le_factorization hb0).mpr h2b)))

lemma fSel_lcm_mul_gcd {n a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    fSel n (Nat.lcm a b) * fSel n (Nat.gcd a b) = fSel n a * fSel n b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  have hlcm_sf : Squarefree (Nat.lcm a b) := squarefree_lcm ha hb
  have hgcd_sf : Squarefree (Nat.gcd a b) := ha.squarefree_of_dvd (Nat.gcd_dvd_left a b)
  rw [fSel_eq_prod_primeFactors hlcm_sf, fSel_eq_prod_primeFactors hgcd_sf,
    fSel_eq_prod_primeFactors ha, fSel_eq_prod_primeFactors hb]
  have hpf_lcm : (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
    ext p
    simp only [Finset.mem_union, Nat.mem_primeFactors]
    constructor
    · intro ⟨hp, hdvd, _⟩
      have hdvd_mul : p ∣ a * b := dvd_trans hdvd (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
      rcases hp.dvd_mul.mp hdvd_mul with h1 | h2
      · left; exact ⟨hp, h1, ha0⟩
      · right; exact ⟨hp, h2, hb0⟩
    · rintro (⟨hp, h1, _⟩ | ⟨hp, h2, _⟩)
      · exact ⟨hp, dvd_trans h1 (Nat.dvd_lcm_left a b), Nat.lcm_ne_zero ha0 hb0⟩
      · exact ⟨hp, dvd_trans h2 (Nat.dvd_lcm_right a b), Nat.lcm_ne_zero ha0 hb0⟩
  have hpf_gcd : (Nat.gcd a b).primeFactors = a.primeFactors ∩ b.primeFactors := by
    ext p
    simp only [Finset.mem_inter, Nat.mem_primeFactors]
    constructor
    · intro ⟨hp, hdvd, _⟩
      exact ⟨⟨hp, dvd_trans hdvd (Nat.gcd_dvd_left a b), ha0⟩,
        ⟨hp, dvd_trans hdvd (Nat.gcd_dvd_right a b), hb0⟩⟩
    · intro ⟨⟨hp, h1, _⟩, ⟨_, h2, _⟩⟩
      exact ⟨hp, Nat.dvd_gcd h1 h2, Nat.gcd_ne_zero_left ha0⟩
  rw [hpf_lcm, hpf_gcd, Finset.prod_union_inter]

lemma sum_divisors_gSel_eq_fSel {n d : ℕ} (hd : Squarefree d) :
    ∑ e ∈ d.divisors, gSel n e = fSel n d := by
  have hd0 : d ≠ 0 := hd.ne_zero
  -- Map `S ⊆ d.primeFactors` to `e = ∏ r ∈ S, r`
  have hbij : ∑ e ∈ d.divisors, gSel n e =
      ∑ S ∈ d.primeFactors.powerset, ∏ r ∈ S, ((r : ℝ) - (omega n r : ℝ)) / (omega n r : ℝ) := by
    symm
    apply Finset.sum_bij (fun S _ => ∏ r ∈ S, r)
    · intro S hS
      have hsub := Finset.mem_powerset.mp hS
      refine Nat.mem_divisors.mpr ⟨?_, hd0⟩
      rw [← Nat.prod_primeFactors_of_squarefree hd]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
    · intro S1 hS1 S2 hS2 heq
      have h1 := Finset.mem_powerset.mp hS1
      have h2 := Finset.mem_powerset.mp hS2
      have hpf : ∀ S, S ⊆ d.primeFactors → (∏ r ∈ S, r).primeFactors = S := by
        intro S
        induction S using Finset.induction_on with
        | empty => intro _; simp
        | insert r T hrT ih =>
          intro hS
          have hTsub : T ⊆ d.primeFactors := Finset.Subset.trans (Finset.subset_insert r T) hS
          have hrP : Nat.Prime r := (Nat.mem_primeFactors.mp (hS (Finset.mem_insert_self r T))).1
          have hTpos : ∏ x ∈ T, x ≠ 0 :=
            ne_of_gt (Finset.prod_pos (fun x hx => (Nat.mem_primeFactors.mp (hTsub hx)).1.pos))
          rw [Finset.prod_insert hrT, Nat.primeFactors_mul hrP.ne_zero hTpos, hrP.primeFactors, ih hTsub]
          ext x; simp
      rw [← hpf S1 h1, ← hpf S2 h2, heq]
    · intro e he
      have hedvd : e ∣ d := (Nat.mem_divisors.mp he).1
      have he_sf : Squarefree e := hd.squarefree_of_dvd hedvd
      refine ⟨e.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hedvd hd0),
        Nat.prod_primeFactors_of_squarefree he_sf⟩
    · intro S hS
      have hsub := Finset.mem_powerset.mp hS
      have hpf : ∀ T, T ⊆ d.primeFactors → (∏ r ∈ T, r).primeFactors = T := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro _; simp
        | insert r T hrT ih =>
          intro hS'
          have hTsub : T ⊆ d.primeFactors := Finset.Subset.trans (Finset.subset_insert r T) hS'
          have hrP : Nat.Prime r := (Nat.mem_primeFactors.mp (hS' (Finset.mem_insert_self r T))).1
          have hTpos : ∏ x ∈ T, x ≠ 0 :=
            ne_of_gt (Finset.prod_pos (fun x hx => (Nat.mem_primeFactors.mp (hTsub hx)).1.pos))
          rw [Finset.prod_insert hrT, Nat.primeFactors_mul hrP.ne_zero hTpos, hrP.primeFactors, ih hTsub]
          ext x; simp
      simp only [gSel, hpf S hsub]
  rw [hbij, ← Finset.prod_one_add]
  have h1 : ∏ r ∈ d.primeFactors, (1 + ((r : ℝ) - (omega n r : ℝ)) / (omega n r : ℝ)) =
      ∏ r ∈ d.primeFactors, (r : ℝ) / (omega n r : ℝ) := by
    apply Finset.prod_congr rfl
    intro r _
    have hom : (omega n r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (omega_pos n r)
    field_simp [hom]; ring
  rw [h1]
  exact (fSel_eq_prod_primeFactors hd).symm

lemma sum_divisors_hSel_eq_fSel_mul_hSel {n d : ℕ} (hd : Squarefree d) (heven : Even n) :
    ∑ e ∈ d.divisors, hSel n e = fSel n d * hSel n d := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hbij : ∑ e ∈ d.divisors, hSel n e =
      ∑ S ∈ d.primeFactors.powerset, ∏ r ∈ S, (omega n r : ℝ) / ((r : ℝ) - (omega n r : ℝ)) := by
    symm
    apply Finset.sum_bij (fun S _ => ∏ r ∈ S, r)
    · intro S hS
      refine Nat.mem_divisors.mpr ⟨?_, hd0⟩
      rw [← Nat.prod_primeFactors_of_squarefree hd]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp hS)
    · intro S1 hS1 S2 hS2 heq
      have hpf : ∀ S, S ⊆ d.primeFactors → (∏ r ∈ S, r).primeFactors = S := by
        intro S
        induction S using Finset.induction_on with
        | empty => intro _; simp
        | insert r T hrT ih =>
          intro hS
          have hTsub : T ⊆ d.primeFactors := Finset.Subset.trans (Finset.subset_insert r T) hS
          have hrP : Nat.Prime r := (Nat.mem_primeFactors.mp (hS (Finset.mem_insert_self r T))).1
          have hTpos : ∏ x ∈ T, x ≠ 0 :=
            ne_of_gt (Finset.prod_pos (fun x hx => (Nat.mem_primeFactors.mp (hTsub hx)).1.pos))
          rw [Finset.prod_insert hrT, Nat.primeFactors_mul hrP.ne_zero hTpos, hrP.primeFactors, ih hTsub]
          ext x; simp
      rw [← hpf S1 (Finset.mem_powerset.mp hS1), ← hpf S2 (Finset.mem_powerset.mp hS2), heq]
    · intro e he
      have hedvd : e ∣ d := (Nat.mem_divisors.mp he).1
      exact ⟨e.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hedvd hd0),
        Nat.prod_primeFactors_of_squarefree (hd.squarefree_of_dvd hedvd)⟩
    · intro S hS
      have hsub := Finset.mem_powerset.mp hS
      have hpf : ∀ T, T ⊆ d.primeFactors → (∏ r ∈ T, r).primeFactors = T := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro _; simp
        | insert r T hrT ih =>
          intro hS'
          have hTsub : T ⊆ d.primeFactors := Finset.Subset.trans (Finset.subset_insert r T) hS'
          have hrP : Nat.Prime r := (Nat.mem_primeFactors.mp (hS' (Finset.mem_insert_self r T))).1
          have hTpos : ∏ x ∈ T, x ≠ 0 :=
            ne_of_gt (Finset.prod_pos (fun x hx => (Nat.mem_primeFactors.mp (hTsub hx)).1.pos))
          rw [Finset.prod_insert hrT, Nat.primeFactors_mul hrP.ne_zero hTpos, hrP.primeFactors, ih hTsub]
          ext x; simp
      simp only [hSel, hpf S hsub]
  rw [hbij, ← Finset.prod_one_add]
  have h1 : ∏ r ∈ d.primeFactors, (1 + (omega n r : ℝ) / ((r : ℝ) - (omega n r : ℝ))) =
      (∏ r ∈ d.primeFactors, (r : ℝ) / (omega n r : ℝ)) * hSel n d := by
    unfold hSel
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r hr
    have hrP := (Nat.mem_primeFactors.mp hr).1
    have h1 := ne_of_gt (r_sub_omega_pos hrP heven)
    have h2 : (omega n r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (omega_pos n r)
    field_simp [h1, h2]; ring
  rw [h1]
  congr 1
  exact (fSel_eq_prod_primeFactors hd).symm

/-- Selberg upper bound for `{ q ∈ Icc 1 X | ∀ r ≤ z prime, ¬ r ∣ q * (n - p * q) }`. -/
lemma selberg_upper_bound {n p z X : ℕ} (heven : Even n) (hp : Nat.Prime p)
    (hz : 1 ≤ z) (hzp : z < p) :
    let D := (Finset.Icc 1 z).filter Squarefree
    let S := ∑ d ∈ D, hSel n d
    (((Finset.Icc 1 X).filter (fun q : ℕ =>
        ∀ r ∈ (Finset.Icc 2 z).filter Nat.Prime,
          ¬ (r : ℤ) ∣ (q : ℤ) * ((n : ℤ) - (p : ℤ) * (q : ℤ)))).card : ℝ) ≤
      (X : ℝ) / S + (z : ℝ) ^ 4 := by
  classical
  intro D S
  have h1D : 1 ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hz⟩, squarefree_one⟩
  have hS_pos : 0 < S :=
    Finset.sum_pos (fun d _ => hSel_pos heven) ⟨1, h1D⟩
  let lam : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * fSel n d *
      (∑ m ∈ D.filter (fun m => d ∣ m), hSel n m) / S
  have hlam1 : lam 1 = 1 := by
    dsimp only [lam]
    have hfilt : D.filter (fun m => 1 ∣ m) = D := by
      ext m; simp
    rw [hfilt, ArithmeticFunction.moebius_apply_one, fSel_one]
    simp [S, ne_of_gt hS_pos]
  -- Bound `|lam d| ≤ 1` for all `d ∈ D`
  have hlam_abs : ∀ d ∈ D, |lam d| ≤ 1 := by
    intro d hd
    have hd_sf : Squarefree d := (Finset.mem_filter.mp hd).2
    have hd_le : d ≤ z := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sf.ne_zero
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hd_sf]
      push_cast; rw [abs_pow]; norm_num
    dsimp only [lam]
    rw [abs_div, abs_of_pos hS_pos, abs_mul, abs_mul, hmu, one_mul,
      abs_of_pos (fSel_pos hd_pos),
      abs_of_nonneg (Finset.sum_nonneg (fun _ _ => le_of_lt (hSel_pos heven)))]
    rw [div_le_one hS_pos]
    let K := D.filter (fun k => k ≤ z / d ∧ Nat.Coprime k d)
    have hsum_m : ∑ m ∈ D.filter (fun m => d ∣ m), hSel n m = hSel n d * ∑ k ∈ K, hSel n k := by
      rw [Finset.mul_sum]
      apply Finset.sum_bij (fun m _ => m / d)
      · intro m hm
        have hmD := (Finset.mem_filter.mp hm).1
        have hdm := (Finset.mem_filter.mp hm).2
        have hm_sf := (Finset.mem_filter.mp hmD).2
        have hm_le := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmD).1).2
        have hkm : d * (m / d) = m := Nat.mul_div_cancel' hdm
        have hk_sf : Squarefree (m / d) := by
          rw [← hkm] at hm_sf; exact hm_sf.squarefree_of_dvd (dvd_mul_left (m / d) d)
        have hk_pos : 1 ≤ m / d := Nat.pos_of_ne_zero hk_sf.ne_zero
        have hk_le : m / d ≤ z / d := Nat.div_le_div_right hm_le
        have hcop : Nat.Coprime (m / d) d := by
          rw [Nat.coprime_comm]
          rw [← hkm] at hm_sf
          exact (Nat.squarefree_mul_iff.mp hm_sf).1
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk_pos, le_trans hk_le (Nat.div_le_self z d)⟩, hk_sf⟩,
           hk_le, hcop⟩
      · intro m1 hm1 m2 hm2 heq
        have h1 := (Finset.mem_filter.mp hm1).2
        have h2 := (Finset.mem_filter.mp hm2).2
        rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
      · intro k hk
        have hkD := (Finset.mem_filter.mp hk).1
        have hk_sf := (Finset.mem_filter.mp hkD).2
        have hk_le := (Finset.mem_filter.mp hk).2.1
        have hcop := (Finset.mem_filter.mp hk).2.2
        have hdk_le : d * k ≤ z := le_trans (Nat.mul_le_mul_left d hk_le) (Nat.mul_div_le z d)
        have hdk_sf : Squarefree (d * k) := Nat.squarefree_mul_iff.mpr ⟨hcop.symm, hd_sf, hk_sf⟩
        have hdk_pos : 1 ≤ d * k := Nat.pos_of_ne_zero hdk_sf.ne_zero
        refine ⟨d * k, Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdk_pos, hdk_le⟩, hdk_sf⟩, dvd_mul_right d k⟩,
          Nat.mul_div_cancel_left k hd_pos⟩
      · intro m hm
        have hmD := (Finset.mem_filter.mp hm).1
        have hdm := (Finset.mem_filter.mp hm).2
        have hm_sf := (Finset.mem_filter.mp hmD).2
        have hkm : d * (m / d) = m := Nat.mul_div_cancel' hdm
        have hcop : Nat.Coprime d (m / d) := by
          rw [← hkm] at hm_sf; exact (Nat.squarefree_mul_iff.mp hm_sf).1
        have hk0 : m / d ≠ 0 := by intro h; rw [h, mul_zero] at hkm; exact hm_sf.ne_zero hkm.symm
        conv_lhs => rw [← hkm]
        exact hSel_mul_of_coprime hcop hd_sf.ne_zero hk0
    rw [hsum_m, ← mul_assoc, ← sum_divisors_hSel_eq_fSel_mul_hSel hd_sf heven,
      Finset.sum_mul_sum]
    have hle_S : ∑ x ∈ d.divisors ×ˢ K, hSel n x.1 * hSel n x.2 ≤ ∑ m ∈ D, hSel n m := by
      have hinj : ∀ x ∈ d.divisors ×ˢ K, ∀ y ∈ d.divisors ×ˢ K, x.1 * x.2 = y.1 * y.2 → x = y := by
        intro ⟨e1, k1⟩ hx ⟨e2, k2⟩ hy heq
        have he1 : e1 ∣ d := (Nat.mem_divisors.mp (Finset.mem_product.mp hx).1).1
        have he2 : e2 ∣ d := (Nat.mem_divisors.mp (Finset.mem_product.mp hy).1).1
        have hk1 : Nat.Coprime k1 d := (Finset.mem_filter.mp (Finset.mem_product.mp hx).2).2.2
        have hk2 : Nat.Coprime k2 d := (Finset.mem_filter.mp (Finset.mem_product.mp hy).2).2.2
        have hgcd1 : Nat.gcd (e1 * k1) d = e1 := by
          rw [hk1.gcd_mul_right_cancel e1, Nat.gcd_eq_left he1]
        have hgcd2 : Nat.gcd (e2 * k2) d = e2 := by
          rw [hk2.gcd_mul_right_cancel e2, Nat.gcd_eq_left he2]
        have he_eq : e1 = e2 := by rw [← hgcd1, heq, hgcd2]
        subst he_eq
        have he1_pos : 0 < e1 := Nat.pos_of_ne_zero (hd_sf.squarefree_of_dvd he1).ne_zero
        have hk_eq : k1 = k2 := Nat.eq_of_mul_eq_mul_left he1_pos heq
        exact Prod.ext rfl hk_eq
      have hmap : (d.divisors ×ˢ K).image (fun x => x.1 * x.2) ⊆ D := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨⟨e, k⟩, hmem, rfl⟩
        have he := (Nat.mem_divisors.mp (Finset.mem_product.mp hmem).1).1
        have hk := Finset.mem_filter.mp (Finset.mem_product.mp hmem).2
        have he_sf : Squarefree e := hd_sf.squarefree_of_dvd he
        have hk_sf : Squarefree k := (Finset.mem_filter.mp hk.1).2
        have hcop_ek : Nat.Coprime e k := (hk.2.2.coprime_dvd_right he).symm
        have hek_sf : Squarefree (e * k) := Nat.squarefree_mul_iff.mpr ⟨hcop_ek, he_sf, hk_sf⟩
        have he_le : e ≤ d := Nat.le_of_dvd hd_pos he
        have hek_le : e * k ≤ z :=
          le_trans (Nat.mul_le_mul he_le hk.2.1) (Nat.mul_div_le z d)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hek_sf.ne_zero, hek_le⟩, hek_sf⟩
      have hsum_eq : ∑ x ∈ d.divisors ×ˢ K, hSel n x.1 * hSel n x.2 =
          ∑ m ∈ (d.divisors ×ˢ K).image (fun x => x.1 * x.2), hSel n m := by
        rw [Finset.sum_image (fun a ha b hb hab => hinj a ha b hb hab)]
        apply Finset.sum_congr rfl
        intro ⟨e, k⟩ hmem
        have he := (Nat.mem_divisors.mp (Finset.mem_product.mp hmem).1).1
        have hk := Finset.mem_filter.mp (Finset.mem_product.mp hmem).2
        have hcop_ek : Nat.Coprime e k := (hk.2.2.coprime_dvd_right he).symm
        exact (hSel_mul_of_coprime hcop_ek (hd_sf.squarefree_of_dvd he).ne_zero
          (Finset.mem_filter.mp hk.1).2.ne_zero).symm
      rw [hsum_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg hmap (fun _ _ _ => le_of_lt (hSel_pos heven))
    rw [← Finset.sum_product']
    exact hle_S
  -- Main Selberg quadratic form identity: `∑_{d1, d2 ∈ D} lam d1 * lam d2 / fSel n (lcm d1 d2) = 1 / S`
  have hquad : ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 / fSel n (Nat.lcm d1 d2) = 1 / S := by
    have h1 : ∀ d1 ∈ D, ∀ d2 ∈ D,
        lam d1 * lam d2 / fSel n (Nat.lcm d1 d2) =
        ∑ e ∈ D.filter (fun e => e ∣ d1 ∧ e ∣ d2),
          gSel n e * (lam d1 / fSel n d1) * (lam d2 / fSel n d2) := by
      intro d1 hd1 d2 hd2
      have hsf1 := (Finset.mem_filter.mp hd1).2
      have hsf2 := (Finset.mem_filter.mp hd2).2
      have hpos1 := fSel_pos (n := n) (Nat.pos_of_ne_zero hsf1.ne_zero)
      have hpos2 := fSel_pos (n := n) (Nat.pos_of_ne_zero hsf2.ne_zero)
      have hposL := fSel_pos (n := n) (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hsf1.ne_zero hsf2.ne_zero))
      have hfg := fSel_lcm_mul_gcd (n := n) hsf1 hsf2
      have hgcd_sf : Squarefree (Nat.gcd d1 d2) := hsf1.squarefree_of_dvd (Nat.gcd_dvd_left d1 d2)
      have hdiv_eq : D.filter (fun e => e ∣ d1 ∧ e ∣ d2) = (Nat.gcd d1 d2).divisors := by
        ext e
        simp only [D, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · intro ⟨_, h1, h2⟩
          exact ⟨Nat.dvd_gcd h1 h2, Nat.gcd_ne_zero_left hsf1.ne_zero⟩
        · intro ⟨he, _⟩
          have he1 : e ∣ d1 := dvd_trans he (Nat.gcd_dvd_left d1 d2)
          have he2 : e ∣ d2 := dvd_trans he (Nat.gcd_dvd_right d1 d2)
          have he_sf : Squarefree e := hsf1.squarefree_of_dvd he1
          have hd1_le : d1 ≤ z := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1).2
          exact ⟨⟨⟨Nat.pos_of_ne_zero he_sf.ne_zero,
            le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hsf1.ne_zero) he1) hd1_le⟩, he_sf⟩, he1, he2⟩
      rw [hdiv_eq, ← Finset.sum_mul, ← Finset.sum_mul, sum_divisors_gSel_eq_fSel hgcd_sf]
      have hmul : fSel n (Nat.gcd d1 d2) / (fSel n d1 * fSel n d2) = 1 / fSel n (Nat.lcm d1 d2) := by
        rw [div_eq_div_iff (ne_of_gt (mul_pos hpos1 hpos2)) (ne_of_gt hposL)]
        linarith
      calc lam d1 * lam d2 / fSel n (Nat.lcm d1 d2)
          = lam d1 * lam d2 * (1 / fSel n (Nat.lcm d1 d2)) := by ring
        _ = lam d1 * lam d2 * (fSel n (Nat.gcd d1 d2) / (fSel n d1 * fSel n d2)) := by rw [hmul]
        _ = fSel n (Nat.gcd d1 d2) * (lam d1 / fSel n d1) * (lam d2 / fSel n d2) := by ring
    have h2 : ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 / fSel n (Nat.lcm d1 d2) =
        ∑ e ∈ D, gSel n e * (∑ d ∈ D.filter (fun d => e ∣ d), lam d / fSel n d) ^ 2 := by
      calc ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 / fSel n (Nat.lcm d1 d2)
          = ∑ d1 ∈ D, ∑ d2 ∈ D, ∑ e ∈ D,
              if e ∣ d1 ∧ e ∣ d2 then gSel n e * (lam d1 / fSel n d1) * (lam d2 / fSel n d2) else 0 := by
            apply Finset.sum_congr rfl; intro d1 hd1
            apply Finset.sum_congr rfl; intro d2 hd2
            rw [h1 d1 hd1 d2 hd2, Finset.sum_filter]
        _ = ∑ e ∈ D, ∑ d1 ∈ D, ∑ d2 ∈ D,
              if e ∣ d1 ∧ e ∣ d2 then gSel n e * (lam d1 / fSel n d1) * (lam d2 / fSel n d2) else 0 := by
            have hswap1 : ∀ d1 ∈ D,
                ∑ d2 ∈ D, ∑ e ∈ D, (if e ∣ d1 ∧ e ∣ d2 then gSel n e * (lam d1 / fSel n d1) * (lam d2 / fSel n d2) else 0) =
                ∑ e ∈ D, ∑ d2 ∈ D, (if e ∣ d1 ∧ e ∣ d2 then gSel n e * (lam d1 / fSel n d1) * (lam d2 / fSel n d2) else 0) :=
              fun d1 _ => Finset.sum_comm
            rw [Finset.sum_congr rfl hswap1, Finset.sum_comm]
        _ = ∑ e ∈ D, gSel n e * (∑ d ∈ D.filter (fun d => e ∣ d), lam d / fSel n d) ^ 2 := by
            apply Finset.sum_congr rfl; intro e _
            symm
            rw [sq, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
            apply Finset.sum_congr rfl; intro d1 _
            by_cases h1e : e ∣ d1
            · rw [if_pos h1e, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
              apply Finset.sum_congr rfl; intro d2 _
              by_cases h2e : e ∣ d2
              · simp [h1e, h2e]; ring
              · simp [h1e, h2e]
            · simp only [h1e, ↓reduceIte, zero_mul, mul_zero]
              symm; apply Finset.sum_eq_zero; intro d2 _; simp [h1e]
    -- Evaluate inner sum by Möbius inversion
    have hinner : ∀ e ∈ D, ∑ d ∈ D.filter (fun d => e ∣ d), lam d / fSel n d =
        ((ArithmeticFunction.moebius e : ℤ) : ℝ) * hSel n e / S := by
      intro e he
      have hsf_e := (Finset.mem_filter.mp he).2
      have hstep : ∑ d ∈ D.filter (fun d => e ∣ d), lam d / fSel n d =
          (∑ m ∈ D.filter (fun m => e ∣ m),
            hSel n m * (∑ d ∈ D.filter (fun d => e ∣ d ∧ d ∣ m),
              ((ArithmeticFunction.moebius d : ℤ) : ℝ))) / S := by
        rw [Finset.sum_div]
        have hrew : ∑ d ∈ D.filter (fun d => e ∣ d), lam d / fSel n d =
            ∑ d ∈ D.filter (fun d => e ∣ d), ∑ m ∈ D.filter (fun m => e ∣ m),
              if d ∣ m then ((ArithmeticFunction.moebius d : ℤ) : ℝ) * hSel n m / S else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdD := (Finset.mem_filter.mp hd).1
          have hed := (Finset.mem_filter.mp hd).2
          have hfpos := fSel_pos (n := n) (Nat.pos_of_ne_zero (Finset.mem_filter.mp hdD).2.ne_zero)
          dsimp only [lam]
          have hcancel : ((ArithmeticFunction.moebius d : ℤ) : ℝ) * fSel n d *
              (∑ m ∈ D.filter (fun m => d ∣ m), hSel n m) / S / fSel n d =
              ∑ m ∈ D.filter (fun m => d ∣ m), ((ArithmeticFunction.moebius d : ℤ) : ℝ) * hSel n m / S := by
            rw [← Finset.sum_div, ← Finset.mul_sum]
            field_simp [ne_of_gt hfpos, ne_of_gt hS_pos]
          rw [hcancel, ← Finset.sum_filter]
          congr 1
          ext m; simp only [Finset.mem_filter]
          exact ⟨fun ⟨hm, hdm⟩ => ⟨⟨hm, dvd_trans hed hdm⟩, hdm⟩, fun ⟨⟨hm, _⟩, hdm⟩ => ⟨hm, hdm⟩⟩
        rw [hrew, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_filter]
        apply Finset.sum_congr
        · ext d; simp only [Finset.mem_filter]; tauto
        · intro d _; ring
      rw [hstep]
      congr 1
      have hm_eval : ∀ m ∈ D.filter (fun m => e ∣ m),
          ∑ d ∈ D.filter (fun d => e ∣ d ∧ d ∣ m), ((ArithmeticFunction.moebius d : ℤ) : ℝ) =
          if m = e then ((ArithmeticFunction.moebius e : ℤ) : ℝ) else 0 := by
        intro m hm
        have hmD := (Finset.mem_filter.mp hm).1
        have hem := (Finset.mem_filter.mp hm).2
        have hsf_m := (Finset.mem_filter.mp hmD).2
        have hm_le := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmD).1).2
        have hme_eq : e * (m / e) = m := Nat.mul_div_cancel' hem
        have hcop_em : Nat.Coprime e (m / e) := by
          rw [← hme_eq] at hsf_m; exact (Nat.squarefree_mul_iff.mp hsf_m).1
        have hsum_k : ∑ d ∈ D.filter (fun d => e ∣ d ∧ d ∣ m), ((ArithmeticFunction.moebius d : ℤ) : ℝ) =
            ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
              ∑ k ∈ (m / e).divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_bij (fun d _ => d / e)
          · intro d hd
            have hed := (Finset.mem_filter.mp hd).2.1
            have hdm := (Finset.mem_filter.mp hd).2.2
            refine Nat.mem_divisors.mpr ⟨?_, by intro h; rw [h, mul_zero] at hme_eq; exact hsf_m.ne_zero hme_eq.symm⟩
            rcases hdm with ⟨t, ht⟩
            have hde := Nat.mul_div_cancel' hed
            refine ⟨t, ?_⟩
            have : e * (d / e * t) = e * (m / e) := by rw [← mul_assoc, hde, ← ht, hme_eq]
            exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hsf_e.ne_zero) this.symm
          · intro d1 hd1 d2 hd2 heq
            have h1 := (Finset.mem_filter.mp hd1).2.1
            have h2 := (Finset.mem_filter.mp hd2).2.1
            rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
          · intro k hk
            have hk_dvd := (Nat.mem_divisors.mp hk).1
            have hek_dvd : e * k ∣ m := hme_eq ▸ Nat.mul_dvd_mul_left e hk_dvd
            have hek_sf : Squarefree (e * k) := hsf_m.squarefree_of_dvd hek_dvd
            have hek_le : e * k ≤ z := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hsf_m.ne_zero) hek_dvd) hm_le
            refine ⟨e * k, Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hek_sf.ne_zero, hek_le⟩, hek_sf⟩,
               dvd_mul_right e k, hek_dvd⟩,
              Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hsf_e.ne_zero)⟩
          · intro d hd
            have hed := (Finset.mem_filter.mp hd).2.1
            have hdm := (Finset.mem_filter.mp hd).2.2
            have hde : e * (d / e) = d := Nat.mul_div_cancel' hed
            have hcop_d : Nat.Coprime e (d / e) := by
              have hdsf := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
              rw [← hde] at hdsf; exact (Nat.squarefree_mul_iff.mp hdsf).1
            conv_lhs => rw [← hde]
            have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_d
            rw [hmul]; push_cast; rfl
        rw [hsum_k]
        have hmob : (∑ k ∈ (m / e).divisors, (ArithmeticFunction.moebius k : ℤ)) =
            if m / e = 1 then 1 else 0 := by
          have h := ArithmeticFunction.moebius_mul_coe_zeta
          have hval := congrArg (fun f => f (m / e)) h
          simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
            ArithmeticFunction.zeta_apply, ArithmeticFunction.one_apply] at hval
          -- Direct `ArithmeticFunction.sum_moebius_eq_one` or `Nat.sum_divisorsAntidiagonal`
          have hsum_eq : ∑ k ∈ (m / e).divisors, (ArithmeticFunction.moebius k : ℤ) =
              ∑ x ∈ (m / e).divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) * (if x.2 = 0 then 0 else 1) := by
            rw [Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius a : ℤ) * (if b = 0 then 0 else 1))]
            apply Finset.sum_congr rfl
            intro k hk
            have hk0 : m / e / k ≠ 0 := by
              have hme0 : m / e ≠ 0 := by intro h0; rw [h0, mul_zero] at hme_eq; exact hsf_m.ne_zero hme_eq.symm
              exact Nat.div_ne_zero_iff.mpr ⟨by intro h0; exact (Nat.mem_divisors.mp hk).2 (by simpa [h0] using (Nat.mem_divisors.mp hk).1),
                Nat.le_of_dvd (Nat.pos_of_ne_zero hme0) (Nat.mem_divisors.mp hk).1⟩
            simp [hk0]
          rw [hsum_eq]
          exact_mod_cast hval
        have hmobR : (∑ k ∈ (m / e).divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ)) =
            if m / e = 1 then 1 else 0 := by
          exact_mod_cast hmob
        rw [hmobR]
        by_cases hme1 : m = e
        · subst hme1
          rw [if_pos rfl, Nat.div_self (Nat.pos_of_ne_zero hsf_e.ne_zero), if_pos rfl, mul_one]
        · have hne1 : m / e ≠ 1 := by
            intro h1; rw [h1, mul_one] at hme_eq; exact hme1 hme_eq.symm
          rw [if_neg hme1, if_neg hne1, mul_zero]
      calc ∑ m ∈ D.filter (fun m => e ∣ m),
            hSel n m * (∑ d ∈ D.filter (fun d => e ∣ d ∧ d ∣ m), ((ArithmeticFunction.moebius d : ℤ) : ℝ))
          = ∑ m ∈ D.filter (fun m => e ∣ m),
              if m = e then hSel n m * ((ArithmeticFunction.moebius e : ℤ) : ℝ) else 0 := by
            apply Finset.sum_congr rfl; intro m hm
            rw [hm_eval m hm]; split_ifs <;> ring
        _ = ((ArithmeticFunction.moebius e : ℤ) : ℝ) * hSel n e := by
            rw [Finset.sum_ite_eq']
            have he_mem : e ∈ D.filter (fun m => e ∣ m) := Finset.mem_filter.mpr ⟨he, dvd_rfl⟩
            rw [if_pos he_mem]; ring
    rw [h2]
    calc ∑ e ∈ D, gSel n e * (∑ d ∈ D.filter (fun d => e ∣ d), lam d / fSel n d) ^ 2
        = ∑ e ∈ D, gSel n e * (((ArithmeticFunction.moebius e : ℤ) : ℝ) * hSel n e / S) ^ 2 := by
          apply Finset.sum_congr rfl; intro e he; rw [hinner e he]
      _ = ∑ e ∈ D, hSel n e / S ^ 2 := by
          apply Finset.sum_congr rfl; intro e he
          have hsf_e := (Finset.mem_filter.mp he).2
          have hmu2 : (((ArithmeticFunction.moebius e : ℤ) : ℝ)) ^ 2 = 1 := by
            rw [ArithmeticFunction.moebius_apply_of_squarefree hsf_e]
            push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
          have hgh := gSel_mul_hSel (n := n) (d := e) heven
          calc gSel n e * (((ArithmeticFunction.moebius e : ℤ) : ℝ) * hSel n e / S) ^ 2
              = (gSel n e * hSel n e) * (((ArithmeticFunction.moebius e : ℤ) : ℝ)) ^ 2 * (hSel n e / S ^ 2) := by ring
            _ = 1 * 1 * (hSel n e / S ^ 2) := by rw [hgh, hmu2]
            _ = hSel n e / S ^ 2 := by ring
      _ = S / S ^ 2 := by rw [← Finset.sum_div]
      _ = 1 / S := by field_simp [ne_of_gt hS_pos]
  -- Now apply Selberg's upper bound: `1 ≤ (∑_{d ∈ D, d ∣ Q(q)} lam d)^2`
  let Q : ℕ → ℤ := fun q => (q : ℤ) * ((n : ℤ) - (p : ℤ) * (q : ℤ))
  have h1 : (((Finset.Icc 1 X).filter (fun q : ℕ =>
      ∀ r ∈ (Finset.Icc 2 z).filter Nat.Prime, ¬ (r : ℤ) ∣ Q q)).card : ℝ) ≤
      ∑ q ∈ Finset.Icc 1 X, (∑ d ∈ D.filter (fun d : ℕ => (d : ℤ) ∣ Q q), lam d) ^ 2 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro q _
    by_cases hq : ∀ r ∈ (Finset.Icc 2 z).filter Nat.Prime, ¬ (r : ℤ) ∣ Q q
    · rw [if_pos hq]
      have honly1 : D.filter (fun d : ℕ => (d : ℤ) ∣ Q q) = {1} := by
        ext d
        simp only [D, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · intro ⟨⟨⟨hd1, hdz⟩, _⟩, hdvd⟩
          by_contra hdne1
          let r := d.minFac
          have hrP : Nat.Prime r := Nat.minFac_prime hdne1
          have hrd : r ∣ d := Nat.minFac_dvd d
          have hrz : r ≤ z := le_trans (Nat.le_of_dvd (by omega) hrd) hdz
          have hr_mem : r ∈ (Finset.Icc 2 z).filter Nat.Prime :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrP.two_le, hrz⟩, hrP⟩
          exact hq r hr_mem (dvd_trans (Int.natCast_dvd_natCast.mpr hrd) hdvd)
        · rintro rfl
          exact ⟨⟨⟨le_rfl, hz⟩, squarefree_one⟩, by simp⟩
      rw [honly1, Finset.sum_singleton, hlam1]; norm_num
    · rw [if_neg hq]; exact sq_nonneg _
  -- Expand the square and swap sums
  have hexpand : ∑ q ∈ Finset.Icc 1 X, (∑ d ∈ D.filter (fun d : ℕ => (d : ℤ) ∣ Q q), lam d) ^ 2 =
      ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
        (((Finset.Icc 1 X).filter (fun q : ℕ => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) := by
    calc ∑ q ∈ Finset.Icc 1 X, (∑ d ∈ D.filter (fun d : ℕ => (d : ℤ) ∣ Q q), lam d) ^ 2
        = ∑ q ∈ Finset.Icc 1 X, ∑ d1 ∈ D, ∑ d2 ∈ D,
            if ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q then lam d1 * lam d2 else 0 := by
          apply Finset.sum_congr rfl; intro q _
          rw [sq, Finset.sum_mul, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro d1 _
          by_cases h1d : (d1 : ℤ) ∣ Q q
          · rw [if_pos h1d, Finset.mul_sum, Finset.sum_filter]
            apply Finset.sum_congr rfl; intro d2 _
            have hlcm_iff : ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q ↔ (d1 : ℤ) ∣ Q q ∧ (d2 : ℤ) ∣ Q q := by
              constructor
              · intro h
                exact ⟨dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left d1 d2)) h,
                  dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right d1 d2)) h⟩
              · rintro ⟨ha, hb⟩
                have ha' : d1 ∣ (Q q).natAbs := Int.natCast_dvd.mp ha
                have hb' : d2 ∣ (Q q).natAbs := Int.natCast_dvd.mp hb
                exact Int.natCast_dvd.mpr (Nat.lcm_dvd ha' hb')
            by_cases h2d : (d2 : ℤ) ∣ Q q
            · simp [h1d, h2d, hlcm_iff.mpr ⟨h1d, h2d⟩]
            · simp [h1d, h2d, show ¬ ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q from fun h => h2d (hlcm_iff.mp h).2]
          · simp only [h1d, ↓reduceIte, zero_mul]
            symm; apply Finset.sum_eq_zero; intro d2 _
            rw [if_neg]; intro h
            exact h1d (dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left d1 d2)) h)
      _ = ∑ d1 ∈ D, ∑ d2 ∈ D, ∑ q ∈ Finset.Icc 1 X,
            if ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q then lam d1 * lam d2 else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro d1 _
          exact Finset.sum_comm
      _ = ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
            (((Finset.Icc 1 X).filter (fun q : ℕ => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) := by
          apply Finset.sum_congr rfl; intro d1 _
          apply Finset.sum_congr rfl; intro d2 _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hexpand] at h1
  -- Split into main term `(X : ℝ) / S` and error term `≤ (z : ℝ)^4`
  have hmain_err : ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
        (((Finset.Icc 1 X).filter (fun q : ℕ => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) ≤
      (X : ℝ) / S + (z : ℝ) ^ 4 := by
    have hsplit : ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
          (((Finset.Icc 1 X).filter (fun q : ℕ => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) =
        (X : ℝ) * (∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 / fSel n (Nat.lcm d1 d2)) +
        ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
          ((((Finset.Icc 1 X).filter (fun q : ℕ => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) -
           ((omega n (Nat.lcm d1 d2) : ℝ) / (Nat.lcm d1 d2 : ℝ)) * (X : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro d1 hd1
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro d2 hd2
      have hlcm0 : (Nat.lcm d1 d2 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.lcm_ne_zero (Finset.mem_filter.mp hd1).2.ne_zero (Finset.mem_filter.mp hd2).2.ne_zero
      have hom0 : (omega n (Nat.lcm d1 d2) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (omega_pos n _)
      unfold fSel; field_simp [hlcm0, hom0]; ring
    rw [hsplit, hquad, mul_one_div]
    gcongr
    have hD_card : (D.card : ℝ) ≤ (z : ℝ) := by
      have : D.card ≤ (Finset.Icc 1 z).card := Finset.card_le_card (Finset.filter_subset _ _)
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : D.card ≤ z)
    calc ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
            ((((Finset.Icc 1 X).filter (fun q : ℕ => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) -
             ((omega n (Nat.lcm d1 d2) : ℝ) / (Nat.lcm d1 d2 : ℝ)) * (X : ℝ))
        ≤ ∑ d1 ∈ D, ∑ d2 ∈ D, (z : ℝ) ^ 2 := by
          apply Finset.sum_le_sum; intro d1 hd1
          apply Finset.sum_le_sum; intro d2 hd2
          have hsf1 := (Finset.mem_filter.mp hd1).2
          have hsf2 := (Finset.mem_filter.mp hd2).2
          have hd1_le : d1 ≤ z := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1).2
          have hd2_le : d2 ≤ z := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd2).1).2
          have hlcm_sf : Squarefree (Nat.lcm d1 d2) := squarefree_lcm hsf1 hsf2
          have hp_cop : Nat.Coprime p (Nat.lcm d1 d2) := by
            refine hp.coprime_iff_not_dvd.mpr ?_
            intro hdvd
            have hmul : p ∣ d1 * d2 := dvd_trans hdvd (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
            rcases hp.dvd_mul.mp hmul with h1 | h2
            · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hsf1.ne_zero) h1; omega
            · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hsf2.ne_zero) h2; omega
          have herr := card_Icc_dvd_quad_error (n := n) (p := p) (d := Nat.lcm d1 d2) (X := X) hlcm_sf hp_cop
          have hom_le : (omega n (Nat.lcm d1 d2) : ℝ) ≤ (z : ℝ) ^ 2 := by
            have h1 := omega_le_self hlcm_sf heven
            have h2 : Nat.lcm d1 d2 ≤ d1 * d2 := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hsf1.ne_zero) (Nat.pos_of_ne_zero hsf2.ne_zero))
              (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
            have h3 : d1 * d2 ≤ z * z := Nat.mul_le_mul hd1_le hd2_le
            have : omega n (Nat.lcm d1 d2) ≤ z ^ 2 := by rw [sq]; omega
            exact_mod_cast this
          calc lam d1 * lam d2 *
                ((((Finset.Icc 1 X).filter (fun q => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) -
                 ((omega n (Nat.lcm d1 d2) : ℝ) / (Nat.lcm d1 d2 : ℝ)) * (X : ℝ))
              ≤ |lam d1 * lam d2 *
                  ((((Finset.Icc 1 X).filter (fun q => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) -
                   ((omega n (Nat.lcm d1 d2) : ℝ) / (Nat.lcm d1 d2 : ℝ)) * (X : ℝ))| := le_abs_self _
            _ = |lam d1| * |lam d2| *
                  |(((Finset.Icc 1 X).filter (fun q => ((Nat.lcm d1 d2 : ℕ) : ℤ) ∣ Q q)).card : ℝ) -
                   ((omega n (Nat.lcm d1 d2) : ℝ) / (Nat.lcm d1 d2 : ℝ)) * (X : ℝ)| := by
                rw [abs_mul, abs_mul]
            _ ≤ 1 * 1 * (omega n (Nat.lcm d1 d2) : ℝ) := by
                gcongr
                · exact hlam_abs d1 hd1
                · exact hlam_abs d2 hd2
            _ ≤ (z : ℝ) ^ 2 := by linarith
      _ = (D.card : ℝ) * ((D.card : ℝ) * (z : ℝ) ^ 2) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (z : ℝ) * ((z : ℝ) * (z : ℝ) ^ 2) := by gcongr
      _ = (z : ℝ) ^ 4 := by ring
  exact le_trans (by simpa only [Q] using h1) hmain_err

/-!
## Part 5: Lower bound on `S(z) = ∑_{d ∈ D} hSel n d`
-/

/-- Harmonic sum lower bound: `log (M + 1) ≤ ∑_{k=1}^{M} 1/k`. -/
lemma log_succ_le_harmonic (M : ℕ) :
    Real.log ((M + 1 : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hstep : Real.log ((M + 2 : ℕ) : ℝ) - Real.log ((M + 1 : ℕ) : ℝ) ≤ 1 / ((M + 1 : ℕ) : ℝ) := by
      have hpos1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
      have hpos2 : (0 : ℝ) < ((M + 2 : ℕ) : ℝ) := by positivity
      rw [← Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)]
      have hlog := Real.log_le_sub_one_of_pos (div_pos hpos2 hpos1)
      have hsub : ((M + 2 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) - 1 = 1 / ((M + 1 : ℕ) : ℝ) := by
        push_cast; field_simp [ne_of_gt (by positivity : (0 : ℝ) < (M : ℝ) + 1)]; ring
      linarith
    linarith

lemma finite_geom_sum_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (N : ℕ) :
    ∑ e ∈ Finset.range N, t ^ e ≤ 1 / (1 - t) := by
  rw [geom_sum_eq (ne_of_lt ht1)]
  have h1 : 0 < 1 - t := by linarith
  have h2 : (t ^ N - 1) / (t - 1) = (1 - t ^ N) / (1 - t) := by
    have hne1 : t - 1 ≠ 0 := by linarith
    have hne2 : 1 - t ≠ 0 := ne_of_gt h1
    field_simp [hne1, hne2]; ring
  rw [h2]
  apply div_le_div_of_nonneg_right _ (le_of_lt h1)
  have : 0 ≤ t ^ N := pow_nonneg ht0 N
  linarith

lemma finite_geom_sum_pos_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, t ^ e ≤ t / (1 - t) := by
  have hrew : ∑ e ∈ Finset.Icc 1 N, t ^ e = t * ∑ e ∈ Finset.range N, t ^ e := by
    rw [Finset.mul_sum]
    apply Finset.sum_bij (fun e _ => e - 1)
    · intro e he; simp only [Finset.mem_Icc, Finset.mem_range] at he ⊢; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
    · intro b hb; refine ⟨b + 1, Finset.mem_Icc.mpr ⟨by omega, by simp at hb; omega⟩, by omega⟩
    · intro e he
      have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      have hsub : e = (e - 1) + 1 := by omega
      conv_lhs => rw [hsub, pow_succ']
  rw [hrew]
  calc t * ∑ e ∈ Finset.range N, t ^ e ≤ t * (1 / (1 - t)) :=
        mul_le_mul_of_nonneg_left (finite_geom_sum_le ht0 ht1 N) ht0
    _ = t / (1 - t) := by ring

/-- Completely multiplicative weight `omegaStar n m = ∏_{r ∈ m.primeFactors, ¬ r ∣ n} 2^(v_r(m))`. -/
def omegaStar (n m : ℕ) : ℕ :=
  ∏ r ∈ m.primeFactors.filter (fun r => ¬ r ∣ n), 2 ^ (m.factorization r)

lemma omegaStar_ge_coprime_divisors (n m : ℕ) (hm : 0 < m) :
    (m.divisors.filter (fun b => Nat.Coprime b n)).card ≤ omegaStar n m := by
  -- Map `b ∈ m.divisors` with `Coprime b n` to `fun r => b.factorization r`
  let P := m.primeFactors.filter (fun r => ¬ r ∣ n)
  let F : ℕ → (r : ℕ) → ℕ := fun b r => b.factorization r
  have hle_prod : (m.divisors.filter (fun b => Nat.Coprime b n)).card ≤
      ∏ r ∈ P, (m.factorization r + 1) := by
    have hcard_pi : (P.pi (fun r => Finset.range (m.factorization r + 1))).card =
        ∏ r ∈ P, (m.factorization r + 1) := by
      rw [Finset.card_pi]
      apply Finset.prod_congr rfl; intro r _; exact Finset.card_range _
    rw [← hcard_pi]
    apply Finset.card_le_card_of_injOn (fun b => fun r _ => b.factorization r)
    · intro b hb
      have hb' := Finset.mem_filter.mp hb
      have hbdvd : b ∣ m := (Nat.mem_divisors.mp hb'.1).1
      rw [Finset.mem_coe, Finset.mem_pi]
      intro r _
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.factorization_le_iff_dvd (Nat.pos_of_dvd_of_pos hbdvd hm).ne' hm.ne' |>.mpr hbdvd r))
    · intro b1 hb1 b2 hb2 heq
      have h1 := Finset.mem_filter.mp hb1
      have h2 := Finset.mem_filter.mp hb2
      have hb1_pos : b1 ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h1.1).1 hm).ne'
      have hb2_pos : b2 ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h2.1).1 hm).ne'
      apply Nat.eq_of_factorization_eq hb1_pos hb2_pos
      intro r
      by_cases hrP : r ∈ P
      · exact congrFun (congrFun heq r) hrP
      · have hzero : ∀ b, b ∣ m → Nat.Coprime b n → b.factorization r = 0 := by
          intro b hbd hcop
          by_contra hne
          have hr_pf : r ∈ b.primeFactors := by
            rw [← Nat.support_factorization]
            exact Finsupp.mem_support_iff.mpr hne
          have hr_m : r ∈ m.primeFactors := Nat.primeFactors_mono hbd hm.ne' hr_pf
          have hr_ndvd : ¬ r ∣ n := by
            intro hrn
            have hd := Nat.dvd_gcd (Nat.mem_primeFactors.mp hr_pf).2.1 hrn
            rw [hcop.gcd_eq_one] at hd
            exact (Nat.mem_primeFactors.mp hr_pf).1.not_dvd_one hd
          exact hrP (Finset.mem_filter.mpr ⟨hr_m, hr_ndvd⟩)
        rw [hzero b1 (Nat.mem_divisors.mp h1.1).1 h1.2, hzero b2 (Nat.mem_divisors.mp h2.1).1 h2.2]
  calc (m.divisors.filter (fun b => Nat.Coprime b n)).card
      ≤ ∏ r ∈ P, (m.factorization r + 1) := hle_prod
    _ ≤ ∏ r ∈ P, 2 ^ (m.factorization r) :=
        Finset.prod_le_prod' (fun r _ => Nat.succ_le_of_lt (Nat.lt_two_pow_self))

/-- Lower bound `∑_{m=1}^{z} omegaStar n m / m ≤ ∑_{d ∈ D} hSel n d`. -/
lemma sum_omegaStar_div_le_S {n z : ℕ} (heven : Even n) :
    ∑ m ∈ Finset.Icc 1 z, (omegaStar n m : ℝ) / (m : ℝ) ≤
      ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, hSel n d := by
  let D := (Finset.Icc 1 z).filter Squarefree
  let rad : ℕ → ℕ := fun m => ∏ r ∈ m.primeFactors, r
  have hrad_mem : ∀ m ∈ Finset.Icc 1 z, rad m ∈ D := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmz : m ≤ z := (Finset.mem_Icc.mp hm).2
    have hsf : Squarefree (rad m) := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hpsq
      have hrad_ne : rad m ≠ 0 := ne_of_gt (Finset.prod_pos (fun r hr => (Nat.mem_primeFactors.mp hr).1.pos))
      have hval : (rad m).factorization p ≤ 1 := by
        dsimp only [rad]
        rw [Nat.factorization_prod (fun r hr => (Nat.mem_primeFactors.mp hr).1.ne_zero),
          finsupp_sum_apply_nat]
        by_cases hpm : p ∈ m.primeFactors
        · rw [Finset.sum_eq_single p]
          · rw [hp.factorization_self]
          · intro r hr hrp
            have hrP := (Nat.mem_primeFactors.mp hr).1
            rw [hrP.factorization, Finsupp.single_eq_of_ne (Ne.symm hrp)]
          · intro h; exact absurd hpm h
        · rw [Finset.sum_eq_zero]
          · omega
          · intro r hr
            have hrP := (Nat.mem_primeFactors.mp hr).1
            have hrne : r ≠ p := fun h => hpm (h ▸ hr)
            rw [hrP.factorization, Finsupp.single_eq_of_ne hrne.symm]
      have h2 : 2 ≤ (rad m).factorization p :=
        (hp.pow_dvd_iff_le_factorization hrad_ne).mp (by simpa [sq] using hpsq)
      omega
    have hdvd : rad m ∣ m := by
      have hcop : Set.Pairwise (↑m.primeFactors : Set ℕ) Nat.Coprime := by
        intro a ha b hb hab
        exact (Nat.coprime_primes (Nat.mem_primeFactors.mp ha).1 (Nat.mem_primeFactors.mp hb).1).mpr hab
      exact nat_prod_dvd_of_coprime hcop (fun r hr => (Nat.mem_primeFactors.mp hr).2.1)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hsf.ne_zero, le_trans (Nat.le_of_dvd (by omega) hdvd) hmz⟩, hsf⟩
  -- Partition `Icc 1 z` by `rad m ∈ D`
  have hpart : ∑ m ∈ Finset.Icc 1 z, (omegaStar n m : ℝ) / (m : ℝ) =
      ∑ d ∈ D, ∑ m ∈ (Finset.Icc 1 z).filter (fun m => rad m = d), (omegaStar n m : ℝ) / (m : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hrad_mem]
  rw [hpart]
  apply Finset.sum_le_sum
  intro d hd
  have hsf_d := (Finset.mem_filter.mp hd).2
  -- For each `m` with `rad m = d`, `m.primeFactors = d.primeFactors` and `1 ≤ m.factorization r ≤ z`
  have hpf_eq : ∀ m ∈ (Finset.Icc 1 z).filter (fun m => rad m = d), m.primeFactors = d.primeFactors := by
    intro m hm
    have hrm := (Finset.mem_filter.mp hm).2
    rw [← hrm]
    dsimp only [rad]
    ext r
    simp only [Nat.mem_primeFactors]
    constructor
    · intro ⟨hr, hrm_dvd, hm0⟩
      refine ⟨hr, Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hr, hrm_dvd, hm0⟩),
        ne_of_gt (Finset.prod_pos (fun q hq => (Nat.mem_primeFactors.mp hq).1.pos))⟩
    · intro ⟨hr, hprod_dvd, _⟩
      obtain ⟨q, hq, hrq⟩ := nat_prime_dvd_finset_prod hr hprod_dvd
      have hqP := (Nat.mem_primeFactors.mp hq).1
      have heq := (Nat.prime_dvd_prime_iff_eq hr hqP).mp hrq
      exact heq ▸ Nat.mem_primeFactors.mp hq
  -- Inject `m` into `d.primeFactors.pi (fun _ => Icc 1 z)` via `r ↦ m.factorization r`
  have hdirect : ∑ m ∈ (Finset.Icc 1 z).filter (fun m => rad m = d), (omegaStar n m : ℝ) / (m : ℝ) ≤
      ∏ r ∈ d.primeFactors, ∑ e ∈ Finset.Icc 1 z, ((omega n r : ℝ) / (r : ℝ)) ^ e := by
    rw [Finset.prod_sum]
    let Φ : ℕ → (r : ℕ) → r ∈ d.primeFactors → ℕ := fun m r _ => m.factorization r
    have hmaps : ∀ m ∈ (Finset.Icc 1 z).filter (fun m => rad m = d),
        Φ m ∈ d.primeFactors.pi (fun _ => Finset.Icc 1 z) := by
      intro m hm
      have hmI := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
      have hpfm := hpf_eq m hm
      rw [Finset.mem_pi]
      intro r hr
      have hrm : r ∈ m.primeFactors := hpfm.symm ▸ hr
      have hrP := (Nat.mem_primeFactors.mp hrm).1
      have hpos : 1 ≤ m.factorization r :=
        Nat.Prime.factorization_pos_of_dvd hrP (by omega) (Nat.mem_primeFactors.mp hrm).2.1
      have hle : m.factorization r ≤ z := by
        have hpow : r ^ (m.factorization r) ≤ m :=
          Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m r)
        have hlt : m.factorization r < 2 ^ (m.factorization r) := Nat.lt_two_pow_self
        have h2pow : 2 ^ (m.factorization r) ≤ r ^ (m.factorization r) :=
          Nat.pow_le_pow_left hrP.two_le _
        omega
      exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
    have hinj : Set.InjOn Φ ((Finset.Icc 1 z).filter (fun m => rad m = d) : Set ℕ) := by
      intro m1 hm1 m2 hm2 heq
      have h1_pos : m1 ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm1).1).1; omega
      have h2_pos : m2 ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm2).1).1; omega
      apply Nat.eq_of_factorization_eq h1_pos h2_pos
      intro r
      by_cases hr : r ∈ d.primeFactors
      · exact congrFun (congrFun heq r) hr
      · have h1 : r ∉ m1.primeFactors := by rwa [hpf_eq m1 hm1]
        have h2 : r ∉ m2.primeFactors := by rwa [hpf_eq m2 hm2]
        rw [factorization_eq_zero_of_not_mem_primeFactors h1,
          factorization_eq_zero_of_not_mem_primeFactors h2]
    have hval : ∀ m ∈ (Finset.Icc 1 z).filter (fun m => rad m = d),
        (omegaStar n m : ℝ) / (m : ℝ) =
        ∏ r ∈ d.primeFactors.attach, ((omega n r.1 : ℝ) / (r.1 : ℝ)) ^ (Φ m r.1 r.2) := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      have hpfm := hpf_eq m hm
      have hm_prod : (m : ℝ) = ∏ r ∈ d.primeFactors.attach, (r.1 : ℝ) ^ (m.factorization r.1) := by
        have hfac : ∏ r ∈ d.primeFactors, r ^ m.factorization r = m := by
          rw [← hpfm]; exact prod_primeFactors_pow_factorization (by omega : m ≠ 0)
        have hfac' : (∏ r ∈ d.primeFactors.attach, r.1 ^ m.factorization r.1) = m := by
          simpa [Finset.prod_attach] using hfac
        have hcast : (m : ℝ) = ((∏ r ∈ d.primeFactors.attach, r.1 ^ m.factorization r.1 : ℕ) : ℝ) := by
          exact_mod_cast hfac'.symm
        rw [hcast, Nat.cast_prod]
        apply Finset.prod_congr rfl; intro r _; rw [Nat.cast_pow]
      have hom_prod : (omegaStar n m : ℝ) =
          ∏ r ∈ d.primeFactors.attach, (omega n r.1 : ℝ) ^ (m.factorization r.1) := by
        unfold omegaStar
        rw [hpfm, Nat.cast_prod]
        have hattach : (∏ r ∈ d.primeFactors.attach, (omega n r.1 : ℝ) ^ m.factorization r.1) =
            ∏ r ∈ d.primeFactors, (omega n r : ℝ) ^ m.factorization r :=
          Finset.prod_attach d.primeFactors (fun r => (omega n r : ℝ) ^ m.factorization r)
        rw [hattach]
        have hsplit : d.primeFactors =
            d.primeFactors.filter (fun r => ¬ r ∣ n) ∪ d.primeFactors.filter (fun r => r ∣ n) := by
          ext r; simp only [Finset.mem_union, Finset.mem_filter]; tauto
        have hdisj : Disjoint (d.primeFactors.filter (fun r => ¬ r ∣ n))
            (d.primeFactors.filter (fun r => r ∣ n)) := by
          rw [Finset.disjoint_left]; intro r h1 h2
          exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
        conv_rhs => rw [hsplit, Finset.prod_union hdisj]
        have h1 : ∏ r ∈ d.primeFactors.filter (fun r => r ∣ n), (omega n r : ℝ) ^ m.factorization r = 1 := by
          apply Finset.prod_eq_one
          intro r hr
          have hrP := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr).1).1
          rw [omega_prime n r hrP, if_pos (Finset.mem_filter.mp hr).2]; norm_num
        rw [h1, mul_one]
        apply Finset.prod_congr rfl
        intro r hr
        have hrP := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr).1).1
        rw [omega_prime n r hrP, if_neg (Finset.mem_filter.mp hr).2]; push_cast; rfl
      rw [hm_prod, hom_prod, ← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro r _
      rw [div_pow]
    have hsum_img : ∑ m ∈ (Finset.Icc 1 z).filter (fun m => rad m = d), (omegaStar n m : ℝ) / (m : ℝ) =
        ∑ f ∈ ((Finset.Icc 1 z).filter (fun m => rad m = d)).image Φ,
          ∏ r ∈ d.primeFactors.attach, ((omega n r.1 : ℝ) / (r.1 : ℝ)) ^ (f r.1 r.2) := by
      rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
      exact Finset.sum_congr rfl hval
    rw [hsum_img]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr hmaps)
      (fun f _ _ => Finset.prod_nonneg (fun _ _ => by positivity))
  exact le_trans hdirect (by
    unfold hSel
    apply real_prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
    intro r hr
    have hrP := (Nat.mem_primeFactors.mp hr).1
    have hpos := r_sub_omega_pos hrP heven
    have ht0 : 0 ≤ (omega n r : ℝ) / (r : ℝ) := by positivity
    have ht1 : (omega n r : ℝ) / (r : ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hrP.pos)]; linarith
    calc ∑ e ∈ Finset.Icc 1 z, ((omega n r : ℝ) / (r : ℝ)) ^ e
        ≤ ((omega n r : ℝ) / (r : ℝ)) / (1 - (omega n r : ℝ) / (r : ℝ)) :=
          finite_geom_sum_pos_le ht0 ht1 z
      _ = (omega n r : ℝ) / ((r : ℝ) - (omega n r : ℝ)) := by
          have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast hrP.ne_zero
          field_simp [hr_ne, ne_of_gt hpos])

/-- Sum of `1/s` over `s ≤ M` whose prime factors all divide `n` is at most `n / n.totient`. -/
lemma sum_smooth_inv_le_div_totient {n M : ℕ} (hn : 1 ≤ n) :
    ∑ s ∈ (Finset.Icc 1 M).filter (fun s => s.primeFactors ⊆ n.primeFactors), (1 : ℝ) / (s : ℝ) ≤
      (n : ℝ) / (n.totient : ℝ) := by
  have h1 : ∑ s ∈ (Finset.Icc 1 M).filter (fun s => s.primeFactors ⊆ n.primeFactors), (1 : ℝ) / (s : ℝ) ≤
      ∏ r ∈ n.primeFactors, ∑ e ∈ Finset.range (M + 1), ((1 : ℝ) / (r : ℝ)) ^ e := by
    rw [Finset.prod_sum]
    let Φ : ℕ → (r : ℕ) → r ∈ n.primeFactors → ℕ := fun s r _ => s.factorization r
    have hmaps : ∀ s ∈ (Finset.Icc 1 M).filter (fun s => s.primeFactors ⊆ n.primeFactors),
        Φ s ∈ n.primeFactors.pi (fun _ => Finset.range (M + 1)) := by
      intro s hs
      have hsI := Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1
      rw [Finset.mem_pi]
      intro r hr
      have hrP := (Nat.mem_primeFactors.mp hr).1
      have hle : s.factorization r ≤ M := by
        have hpow : r ^ (s.factorization r) ≤ s := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd s r)
        have hlt : s.factorization r < 2 ^ (s.factorization r) := Nat.lt_two_pow_self
        have h2pow : 2 ^ (s.factorization r) ≤ r ^ (s.factorization r) := Nat.pow_le_pow_left hrP.two_le _
        omega
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
    have hinj : Set.InjOn Φ ((Finset.Icc 1 M).filter (fun s => s.primeFactors ⊆ n.primeFactors) : Set ℕ) := by
      intro s1 hs1 s2 hs2 heq
      have h1_pos : s1 ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs1).1).1; omega
      have h2_pos : s2 ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs2).1).1; omega
      apply Nat.eq_of_factorization_eq h1_pos h2_pos
      intro r
      by_cases hr : r ∈ n.primeFactors
      · exact congrFun (congrFun heq r) hr
      · have h1 : r ∉ s1.primeFactors := fun h => hr ((Finset.mem_filter.mp hs1).2 h)
        have h2 : r ∉ s2.primeFactors := fun h => hr ((Finset.mem_filter.mp hs2).2 h)
        rw [factorization_eq_zero_of_not_mem_primeFactors h1,
          factorization_eq_zero_of_not_mem_primeFactors h2]
    have hval : ∀ s ∈ (Finset.Icc 1 M).filter (fun s => s.primeFactors ⊆ n.primeFactors),
        (1 : ℝ) / (s : ℝ) =
        ∏ r ∈ n.primeFactors.attach, ((1 : ℝ) / (r.1 : ℝ)) ^ (Φ s r.1 r.2) := by
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
      have hsub := (Finset.mem_filter.mp hs).2
      have hs_prod : (s : ℝ) = ∏ r ∈ n.primeFactors.attach, (r.1 : ℝ) ^ (s.factorization r.1) := by
        have hfac : ∏ r ∈ s.primeFactors, r ^ s.factorization r = s :=
          prod_primeFactors_pow_factorization (by omega : s ≠ 0)
        have hprod_ext : ∏ r ∈ s.primeFactors, r ^ s.factorization r =
            ∏ r ∈ n.primeFactors, r ^ s.factorization r := by
          apply Finset.prod_subset hsub
          intro r _ hrnot
          rw [factorization_eq_zero_of_not_mem_primeFactors hrnot, pow_zero]
        have hfac' : (∏ r ∈ n.primeFactors.attach, r.1 ^ s.factorization r.1) = s := by
          rw [hprod_ext] at hfac
          simpa [Finset.prod_attach] using hfac
        have hcast : (s : ℝ) = ((∏ r ∈ n.primeFactors.attach, r.1 ^ s.factorization r.1 : ℕ) : ℝ) := by
          exact_mod_cast hfac'.symm
        rw [hcast, Nat.cast_prod]
        apply Finset.prod_congr rfl; intro r _; rw [Nat.cast_pow]
      rw [hs_prod, one_div, ← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro r _
      rw [one_div, inv_pow]
    have hsum_img : ∑ s ∈ (Finset.Icc 1 M).filter (fun s => s.primeFactors ⊆ n.primeFactors), (1 : ℝ) / (s : ℝ) =
        ∑ f ∈ ((Finset.Icc 1 M).filter (fun s => s.primeFactors ⊆ n.primeFactors)).image Φ,
          ∏ r ∈ n.primeFactors.attach, ((1 : ℝ) / (r.1 : ℝ)) ^ (f r.1 r.2) := by
      rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
      exact Finset.sum_congr rfl hval
    rw [hsum_img]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr hmaps)
      (fun _ _ _ => Finset.prod_nonneg (fun _ _ => by positivity))
  have h2 : ∏ r ∈ n.primeFactors, ∑ e ∈ Finset.range (M + 1), ((1 : ℝ) / (r : ℝ)) ^ e ≤
      ∏ r ∈ n.primeFactors, (1 - (1 : ℝ) / (r : ℝ))⁻¹ := by
    apply real_prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
    intro r hr
    have hrP := (Nat.mem_primeFactors.mp hr).1
    have ht1 : (1 : ℝ) / (r : ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hrP.pos)]; exact_mod_cast hrP.one_lt
    simpa [one_div] using finite_geom_sum_le (t := (1 : ℝ) / (r : ℝ)) (by positivity) ht1 (M + 1)
  have h3 : ∏ r ∈ n.primeFactors, (1 - (1 : ℝ) / (r : ℝ))⁻¹ = (n : ℝ) / (n.totient : ℝ) := by
    rw [Finset.prod_inv_distrib, ← totient_div_eq_prod n (by omega), inv_div]
  linarith

/-- Lower bound on `∑_{b ≤ M, Coprime b n} 1/b ≥ (n.totient / n) * log (M + 1)`. -/
lemma sum_coprime_inv_ge {n M : ℕ} (hn : 1 ≤ n) :
    ((n.totient : ℝ) / (n : ℝ)) * Real.log ((M + 1 : ℕ) : ℝ) ≤
      ∑ b ∈ (Finset.Icc 1 M).filter (fun b => Nat.Coprime b n), (1 : ℝ) / (b : ℝ) := by
  let S_sm := (Finset.Icc 1 M).filter (fun s => s.primeFactors ⊆ n.primeFactors)
  let S_cp := (Finset.Icc 1 M).filter (fun b => Nat.Coprime b n)
  have hcov : Finset.Icc 1 M ⊆ (S_sm ×ˢ S_cp).image (fun x : ℕ × ℕ => x.1 * x.2) := by
    intro k hk
    have hkI := Finset.mem_Icc.mp hk
    let s := ∏ r ∈ k.primeFactors.filter (fun r => r ∣ n), r ^ (k.factorization r)
    let b := ∏ r ∈ k.primeFactors.filter (fun r => ¬ r ∣ n), r ^ (k.factorization r)
    have hsb : s * b = k := by
      have hfac : ∏ r ∈ k.primeFactors, r ^ k.factorization r = k :=
        prod_primeFactors_pow_factorization (by omega : k ≠ 0)
      have hsplit : k.primeFactors =
          k.primeFactors.filter (fun r => r ∣ n) ∪ k.primeFactors.filter (fun r => ¬ r ∣ n) := by
        ext r; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      have hdisj : Disjoint (k.primeFactors.filter (fun r => r ∣ n))
          (k.primeFactors.filter (fun r => ¬ r ∣ n)) := by
        rw [Finset.disjoint_left]; intro r h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      dsimp only [s, b]
      rw [← Finset.prod_union hdisj, ← hsplit]
      exact hfac
    have hs_pos : 1 ≤ s := Finset.prod_pos (fun r hr => pow_pos (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr).1).1.pos _)
    have hb_pos : 1 ≤ b := Finset.prod_pos (fun r hr => pow_pos (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hr).1).1.pos _)
    have hs_le : s ≤ M := le_trans (Nat.le_of_dvd (by omega) (hsb ▸ dvd_mul_right s b)) hkI.2
    have hb_le : b ≤ M := le_trans (Nat.le_of_dvd (by omega) (hsb ▸ dvd_mul_left b s)) hkI.2
    have hs_sub : s.primeFactors ⊆ n.primeFactors := by
      intro r hr
      have hrP := (Nat.mem_primeFactors.mp hr).1
      have hrd := (Nat.mem_primeFactors.mp hr).2.1
      obtain ⟨q, hq, hrq⟩ := nat_prime_dvd_finset_prod hrP hrd
      have hq' := Finset.mem_filter.mp hq
      have hqP := (Nat.mem_primeFactors.mp hq'.1).1
      have heq := (Nat.prime_dvd_prime_iff_eq hrP hqP).mp (hrP.dvd_of_dvd_pow hrq)
      exact Nat.mem_primeFactors.mpr ⟨hrP, heq ▸ hq'.2, by omega⟩
    have hb_cop : Nat.Coprime b n := by
      refine Nat.coprime_of_dvd (fun r hr hrb hrn => ?_)
      obtain ⟨q, hq, hrq⟩ := nat_prime_dvd_finset_prod hr hrb
      have hq' := Finset.mem_filter.mp hq
      have hqP := (Nat.mem_primeFactors.mp hq'.1).1
      have heq := (Nat.prime_dvd_prime_iff_eq hr hqP).mp (hr.dvd_of_dvd_pow hrq)
      exact hq'.2 (heq ▸ hrn)
    exact Finset.mem_image.mpr ⟨(s, b), Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hs_pos, hs_le⟩, hs_sub⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb_pos, hb_le⟩, hb_cop⟩⟩, hsb⟩
  have hsum_le : ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ≤
      (∑ s ∈ S_sm, (1 : ℝ) / (s : ℝ)) * (∑ b ∈ S_cp, (1 : ℝ) / (b : ℝ)) := by
    calc ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)
        ≤ ∑ k ∈ (S_sm ×ˢ S_cp).image (fun x : ℕ × ℕ => x.1 * x.2), (1 : ℝ) / (k : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ => by positivity)
      _ ≤ ∑ x ∈ S_sm ×ˢ S_cp, (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) :=
          Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
      _ = (∑ s ∈ S_sm, (1 : ℝ) / (s : ℝ)) * (∑ b ∈ S_cp, (1 : ℝ) / (b : ℝ)) := by
          rw [Finset.sum_product, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro s _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _
          rw [Nat.cast_mul]; ring
  have hharm := log_succ_le_harmonic M
  have hsm := sum_smooth_inv_le_div_totient (n := n) (M := M) hn
  have hcp_nn : 0 ≤ ∑ b ∈ S_cp, (1 : ℝ) / (b : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
  have htot_pos : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmul : Real.log ((M + 1 : ℕ) : ℝ) ≤ ((n : ℝ) / (n.totient : ℝ)) * (∑ b ∈ S_cp, (1 : ℝ) / (b : ℝ)) :=
    le_trans (le_trans hharm hsum_le) (mul_le_mul_of_nonneg_right hsm hcp_nn)
  have hratio_pos : 0 < (n.totient : ℝ) / (n : ℝ) := div_pos htot_pos hn_pos
  have hmul2 := mul_le_mul_of_nonneg_left hmul (le_of_lt hratio_pos)
  have hcancel : ((n.totient : ℝ) / (n : ℝ)) * ((n : ℝ) / (n.totient : ℝ)) = 1 := by
    field_simp [ne_of_gt htot_pos, ne_of_gt hn_pos]
  rw [← mul_assoc, hcancel, one_mul] at hmul2
  exact hmul2

/-- Selberg denominator lower bound: `S(z) ≥ (n.totient / n) * (log (√z + 1))^2`. -/
lemma S_lower_bound {n z : ℕ} (hn : 1 ≤ n) (heven : Even n) :
    ((n.totient : ℝ) / (n : ℝ)) * (Real.log ((Nat.sqrt z + 1 : ℕ) : ℝ)) ^ 2 ≤
      ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, hSel n d := by
  let M := Nat.sqrt z
  let S_cp := (Finset.Icc 1 M).filter (fun b => Nat.Coprime b n)
  have hprod_le : (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) *
      (∑ b ∈ S_cp, (1 : ℝ) / (b : ℝ)) ≤
      ∑ m ∈ Finset.Icc 1 z, (omegaStar n m : ℝ) / (m : ℝ) := by
    have hrew : (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) * (∑ b ∈ S_cp, (1 : ℝ) / (b : ℝ)) =
        ∑ x ∈ Finset.Icc 1 M ×ˢ S_cp, (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _
      push_cast; ring
    rw [hrew]
    have hmaps : ∀ x ∈ Finset.Icc 1 M ×ˢ S_cp, x.1 * x.2 ∈ Finset.Icc 1 z := by
      intro ⟨a, b⟩ hx
      have ha := Finset.mem_Icc.mp (Finset.mem_product.mp hx).1
      have hb := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp hx).2).1
      have hmul_le : a * b ≤ M * M := Nat.mul_le_mul ha.2 hb.2
      have hMsq : M * M ≤ z := Nat.sqrt_le z
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos ha.1 hb.1, le_trans hmul_le hMsq⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_le_sum
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hfiber : ∑ x ∈ (Finset.Icc 1 M ×ˢ S_cp).filter (fun x => x.1 * x.2 = m),
        (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) =
        (((Finset.Icc 1 M ×ˢ S_cp).filter (fun x => x.1 * x.2 = m)).card : ℝ) / (m : ℝ) := by
      have heq : ∑ x ∈ (Finset.Icc 1 M ×ˢ S_cp).filter (fun x => x.1 * x.2 = m),
          (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) =
          ∑ _x ∈ (Finset.Icc 1 M ×ˢ S_cp).filter (fun x => x.1 * x.2 = m), (1 : ℝ) / (m : ℝ) :=
        Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])
      rw [heq, Finset.sum_const, nsmul_eq_mul]; ring
    rw [hfiber]
    apply div_le_div_of_nonneg_right _ (by exact_mod_cast (by omega : 0 ≤ m))
    have hcard_le : ((Finset.Icc 1 M ×ˢ S_cp).filter (fun x => x.1 * x.2 = m)).card ≤
        (m.divisors.filter (fun b => Nat.Coprime b n)).card := by
      apply Finset.card_le_card_of_injOn (fun x => x.2)
      · intro ⟨a, b⟩ hx
        have hx' := Finset.mem_filter.mp hx
        have hcop := (Finset.mem_filter.mp (Finset.mem_product.mp hx'.1).2).2
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨a, by linarith [hx'.2]⟩, by omega⟩, hcop⟩
      · intro ⟨a1, b1⟩ hx1 ⟨a2, b2⟩ hx2 hb_eq
        dsimp only at hb_eq
        subst hb_eq
        have h1 := (Finset.mem_filter.mp hx1).2
        have h2 := (Finset.mem_filter.mp hx2).2
        have hb_pos : 0 < b1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx1).1).2).1).1
        have ha_eq : a1 = a2 := Nat.eq_of_mul_eq_mul_right hb_pos (h1.trans h2.symm)
        exact Prod.ext ha_eq rfl
    exact_mod_cast le_trans hcard_le (omegaStar_ge_coprime_divisors n m (by omega))
  have h1 := log_succ_le_harmonic M
  have h2 := sum_coprime_inv_ge (n := n) (M := M) hn
  have h3 := sum_omegaStar_div_le_S (n := n) (z := z) heven
  have hlog_nn : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M + 1))
  have htot_nn : 0 ≤ (n.totient : ℝ) / (n : ℝ) := by positivity
  calc ((n.totient : ℝ) / (n : ℝ)) * (Real.log ((M + 1 : ℕ) : ℝ)) ^ 2
      = Real.log ((M + 1 : ℕ) : ℝ) * (((n.totient : ℝ) / (n : ℝ)) * Real.log ((M + 1 : ℕ) : ℝ)) := by ring
    _ ≤ (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) * (∑ b ∈ S_cp, (1 : ℝ) / (b : ℝ)) :=
        mul_le_mul h1 h2 (mul_nonneg htot_nn hlog_nn) (Finset.sum_nonneg (fun _ _ => by positivity))
    _ ≤ ∑ m ∈ Finset.Icc 1 z, (omegaStar n m : ℝ) / (m : ℝ) := hprod_le
    _ ≤ ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, hSel n d := h3

/-!
## Part 6: Final Assembly for `Taskd4c2c458d1b6958628c99f53`
-/

lemma card_primeFactors_gt_cbrt_le_two (n : ℕ) (hn : 1 ≤ n) :
    (n.primeFactors.filter (fun p => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < p)).card ≤ 2 := by
  by_contra h
  push_neg at h
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.mp h
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  have hr' := Finset.mem_filter.mp hr
  have hpP := (Nat.mem_primeFactors.mp hp'.1).1
  have hqP := (Nat.mem_primeFactors.mp hq'.1).1
  have hrP := (Nat.mem_primeFactors.mp hr'.1).1
  have hpd := (Nat.mem_primeFactors.mp hp'.1).2.1
  have hqd := (Nat.mem_primeFactors.mp hq'.1).2.1
  have hrd := (Nat.mem_primeFactors.mp hr'.1).2.1
  have hcop_pq : Nat.Coprime p q := (Nat.coprime_primes hpP hqP).mpr hpq
  have hcop_pqr : Nat.Coprime (p * q) r :=
    Nat.Coprime.mul_left ((Nat.coprime_primes hpP hrP).mpr hpr) ((Nat.coprime_primes hqP hrP).mpr hqr)
  have hdvd : p * q * r ∣ n := hcop_pqr.mul_dvd_of_dvd_of_dvd (hcop_pq.mul_dvd_of_dvd_of_dvd hpd hqd) hrd
  have hle : (p * q * r : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_dvd (by omega) hdvd
  have h1 : (n : ℝ) ^ (1 / 3 : ℝ) < (p : ℝ) := (Nat.floor_lt (by positivity)).mp hp'.2
  have h2 : (n : ℝ) ^ (1 / 3 : ℝ) < (q : ℝ) := (Nat.floor_lt (by positivity)).mp hq'.2
  have h3 : (n : ℝ) ^ (1 / 3 : ℝ) < (r : ℝ) := (Nat.floor_lt (by positivity)).mp hr'.2
  have hpow : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hnn : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hgt : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 < (p : ℝ) * (q : ℝ) * (r : ℝ) := by
    have h12 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 < (p : ℝ) * (q : ℝ) := by
      rw [sq]; exact mul_lt_mul'' h1 h2 hnn hnn
    have h123 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 * (n : ℝ) ^ (1 / 3 : ℝ) < (p : ℝ) * (q : ℝ) * (r : ℝ) :=
      mul_lt_mul'' h12 h3 (sq_nonneg _) hnn
    linarith [show ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 * (n : ℝ) ^ (1 / 3 : ℝ) by ring]
  linarith

lemma dyadic_tail_bound {n T : ℕ} (hn : 10000 ≤ n) (hT_ge2 : 2 ≤ T)
    (hL_ge : (1000 : ℝ) ≤ Real.log (n : ℝ))
    (hT_ge_exp : Real.exp (Real.log (n : ℝ) / 2 - 2 * (Real.log (n : ℝ)) ^ (2 / 3 : ℝ)) - 1 < (T : ℝ))
    (hlogT_ge : Real.log (n : ℝ) / 5 ≤ Real.log (T : ℝ)) :
    ∑ p ∈ (Finset.Ioc T (Nat.sqrt n)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      100 / (Real.log (n : ℝ)) ^ (1 / 3 : ℝ) := by
  set L : ℝ := Real.log (n : ℝ)
  have hL_pos : 0 < L := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL13 : (10 : ℝ) ≤ L ^ (1 / 3 : ℝ) := by
    have h1 : (10 : ℝ) ^ (3 : ℝ) ≤ L := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num; linarith
    calc (10 : ℝ) = ((10 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ L ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hL23_eq : L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) = L := by
    rw [← Real.rpow_add hL_pos]; norm_num
  let K : ℕ := ⌊4 * L ^ (2 / 3 : ℝ)⌋₊ + 1
  have hK_ge : 4 * L ^ (2 / 3 : ℝ) ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one (4 * L ^ (2 / 3 : ℝ)); dsimp only [K]; push_cast; linarith
  have hK_le : (K : ℝ) ≤ 5 * L ^ (2 / 3 : ℝ) := by
    have h1 : (⌊4 * L ^ (2 / 3 : ℝ)⌋₊ : ℝ) ≤ 4 * L ^ (2 / 3 : ℝ) := Nat.floor_le (by positivity)
    have h2 : (1 : ℝ) ≤ L ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by positivity)
    dsimp only [K]; push_cast; linarith
  have hsqrt_le_2K : Nat.sqrt n ≤ 2 ^ K * T := by
    have h1 : (Nat.sqrt n : ℝ) ≤ Real.exp (L / 2) := by
      have hsq : ((Nat.sqrt n : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
      have hexp : Real.exp (L / 2) ^ 2 = (n : ℝ) := by
        rw [← Real.exp_nat_mul]
        have : ((2 : ℕ) : ℝ) * (L / 2) = L := by ring
        rw [this, Real.exp_log hn_pos]
      nlinarith [Real.exp_pos (L / 2)]
    have h2 : Real.exp (L / 2 - 2 * L ^ (2 / 3 : ℝ)) ≤ 2 * (T : ℝ) := by
      have hge2 : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT_ge2
      linarith
    have h3 : Real.exp (2 * L ^ (2 / 3 : ℝ) + 1) ≤ (2 : ℝ) ^ K := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      have hL23_ge : (2 : ℝ) ≤ L ^ (2 / 3 : ℝ) := by
        have h1' : (2 : ℝ) ≤ L ^ (1 / 3 : ℝ) := by linarith
        have h2' : L ^ (1 / 3 : ℝ) ≤ L ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        linarith
      have hlog2' : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      calc 2 * L ^ (2 / 3 : ℝ) + 1
          ≤ 2 * L ^ (2 / 3 : ℝ) + (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by linarith
        _ = (4 * L ^ (2 / 3 : ℝ)) * (2 / 3 : ℝ) := by ring
        _ ≤ (K : ℝ) * Real.log 2 := mul_le_mul hK_ge hlog2' (by norm_num) (by positivity)
        _ = Real.log 2 * (K : ℝ) := mul_comm _ _
    have h4 : Real.exp (L / 2) ≤ (2 : ℝ) ^ K * (T : ℝ) := by
      have hexp2 : Real.exp 1 ≥ 2 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc Real.exp (L / 2)
          = Real.exp (2 * L ^ (2 / 3 : ℝ)) * Real.exp (L / 2 - 2 * L ^ (2 / 3 : ℝ)) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (2 * L ^ (2 / 3 : ℝ)) * (2 * (T : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos _))
        _ ≤ Real.exp (2 * L ^ (2 / 3 : ℝ)) * (Real.exp 1 * (T : ℝ)) := by gcongr
        _ = Real.exp (2 * L ^ (2 / 3 : ℝ) + 1) * (T : ℝ) := by rw [Real.exp_add]; ring
        _ ≤ (2 : ℝ) ^ K * (T : ℝ) := mul_le_mul_of_nonneg_right h3 (by positivity)
    exact_mod_cast le_trans h1 h4
  have hstep := sum_inv_primes_dyadic hT_ge2 hsqrt_le_2K
  have hlog4_le : Real.log 4 ≤ 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith [Real.log_two_lt_d9]
  calc ∑ p ∈ (Finset.Ioc T (Nat.sqrt n)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ (K : ℝ) * (2 * Real.log 4) / Real.log (T : ℝ) := hstep
    _ ≤ (5 * L ^ (2 / 3 : ℝ)) * 4 / (L / 5) := by
        apply div_le_div₀ (by positivity)
        · exact mul_le_mul hK_le (by linarith) (by positivity) (by positivity)
        · positivity
        · exact hlogT_ge
    _ = 100 * (L ^ (2 / 3 : ℝ) / L) := by ring
    _ = 100 / L ^ (1 / 3 : ℝ) := by
        have hne : L ^ (1 / 3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
        have hL_ne : L ≠ 0 := ne_of_gt hL_pos
        field_simp [hne, hL_ne]
        linarith [hL23_eq]

lemma x4_lower_bound {n : ℕ} (hn : 10000 ≤ n) (heven : Even n) :
    (Real.exp (-18) / 32) * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤
      ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
        ∏ p ∈ ((Finset.Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n),
          ((1 : ℝ) - (2 : ℝ) / (p : ℝ)) := by
  set L : ℝ := Real.log (n : ℝ)
  have hsqrt_ge3 : 3 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hcard_x1 : (n : ℝ) / 4 ≤ ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) := by
    rw [Nat.card_Icc]
    have h1 : n < 4 * (n / 4 + 1) := Nat.lt_mul_div_succ n (by norm_num : 0 < 4)
    have h2 : (n : ℝ) / 4 ≤ ((n / 4 : ℕ) : ℝ) + 1 := by
      have h1' : (n : ℝ) < 4 * (((n / 4 : ℕ) : ℝ) + 1) := by exact_mod_cast h1
      linarith
    have h3 : n / 4 + 1 ≤ 2 * n / 3 + 1 - (n + 2) / 3 := by omega
    have h4 : ((n / 4 : ℕ) : ℝ) + 1 ≤ ((2 * n / 3 + 1 - (n + 2) / 3 : ℕ) : ℝ) := by exact_mod_cast h3
    linarith
  have hprod_lb := sieve_prod_lower_bound (n := n) (by omega) heven
  have hmert := prod_one_sub_two_div_ge hsqrt_ge3
  have hlog_sqrt : Real.log (Nat.sqrt n : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt n)) (by exact_mod_cast Nat.sqrt_le_self n)
  have hlog_sqrt_pos : 0 < Real.log (Nat.sqrt n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.sqrt n))
  have hmert' : Real.exp (-18) / L ^ 2 ≤
      ∏ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime, (1 - (2 : ℝ) / (p : ℝ)) :=
    le_trans (div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) (sq_pos_of_pos hlog_sqrt_pos)
      (pow_le_pow_left₀ (le_of_lt hlog_sqrt_pos) hlog_sqrt 2)) hmert
  have htot_nn : 0 ≤ (n : ℝ) / (n.totient : ℝ) := by positivity
  have hprod_ge : (Real.exp (-18) / 8) * ((n : ℝ) / (n.totient : ℝ)) / L ^ 2 ≤
      ((n.totient : ℝ) / (n : ℝ)) *
        (∏ p ∈ ((Finset.Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - (2 : ℝ) / (p : ℝ))) := by
    have hstep := mul_le_mul_of_nonneg_left hmert' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) htot_nn)
    have hrew : (1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * (Real.exp (-18) / L ^ 2) =
        (Real.exp (-18) / 8) * ((n : ℝ) / (n.totient : ℝ)) / L ^ 2 := by ring
    linarith
  have hrew_rhs : ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
      ∏ p ∈ ((Finset.Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n), ((1 : ℝ) - (2 : ℝ) / (p : ℝ)) =
      ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) * (((n.totient : ℝ) / (n : ℝ)) *
        ∏ p ∈ ((Finset.Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n), ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) := by
    ring
  rw [hrew_rhs]
  calc (Real.exp (-18) / 32) * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)
      = ((n : ℝ) / 4) * ((Real.exp (-18) / 8) * ((n : ℝ) / (n.totient : ℝ)) / L ^ 2) := by ring
    _ ≤ ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) * (((n.totient : ℝ) / (n : ℝ)) *
          ∏ p ∈ ((Finset.Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n), ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) :=
        mul_le_mul hcard_x1 hprod_ge (by positivity) (by positivity)

lemma final_combine_bound {n T z : ℕ} {S Psum x4n A : ℝ}
    (hn : 10000 ≤ n) (hA : A = (1000000 : ℝ) * 1000000 * 1000000 * 100)
    (hL_ge_A : A ≤ Real.log (n : ℝ))
    (hL13 : A ≤ (Real.log (n : ℝ)) ^ (1 / 3 : ℝ))
    (hT_ge_n15 : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (T : ℝ))
    (hz_le_rpow : (z : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ))
    (hS_ge : ((n.totient : ℝ) / (n : ℝ)) * (Real.log (n : ℝ) / 30) ^ 2 ≤ S)
    (hPsum_nn : 0 ≤ Psum) (hPsum_le : Psum ≤ 100 / (Real.log (n : ℝ)) ^ (1 / 3 : ℝ))
    (hx4_ge : (Real.exp (-18) / 32) * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤ x4n) :
    4 * ((n : ℝ) / (T : ℝ)) + 2 * ((n : ℝ) / S) * Psum + 2 * (Nat.sqrt n : ℝ) * (z : ℝ) ^ 4 ≤
      (1 / 500 : ℝ) * x4n := by
  set L : ℝ := Real.log (n : ℝ)
  have hA_pos : 0 < A := by rw [hA]; norm_num
  have hL_pos : 0 < L := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have htot_ge1 : (1 : ℝ) ≤ (n : ℝ) / (n.totient : ℝ) := by
    rw [one_le_div (by exact_mod_cast Nat.totient_pos.mpr (by omega))]
    exact_mod_cast Nat.totient_le n
  have h_inv_S : (n : ℝ) / S ≤ 900 * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2) := by
    have hden_pos : 0 < ((n.totient : ℝ) / (n : ℝ)) * (L / 30) ^ 2 := by
      have : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      positivity
    have h1 := div_le_div_of_nonneg_left (le_of_lt hn_pos) hden_pos hS_ge
    have h2 : (n : ℝ) / (((n.totient : ℝ) / (n : ℝ)) * (L / 30) ^ 2) =
        900 * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2) := by
      have htot_ne : (n.totient : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr (by omega))
      field_simp [htot_ne, ne_of_gt hn_pos, ne_of_gt hL_pos]; ring
    linarith
  have hexp18 : (1 : ℝ) / (400000000 : ℝ) ≤ Real.exp (-18) := by
    rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos 18)]
    have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    calc Real.exp 18 = (Real.exp 1) ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ 18 := pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he3 18
      _ ≤ 400000000 := by norm_num
  let C_x4 : ℝ := 32 * 400000000
  have hbase_le : ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2) ≤ C_x4 * x4n := by
    have h1 : ((1 : ℝ) / C_x4) * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2) ≤ x4n := by
      have hratio : (1 : ℝ) / C_x4 ≤ Real.exp (-18) / 32 := by dsimp only [C_x4]; linarith
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio (by positivity : (0 : ℝ) ≤ (n : ℝ) / (n.totient : ℝ)))
        (by positivity : (0 : ℝ) ≤ (n : ℝ) / L ^ 2)
      linarith
    have hCpos : (0 : ℝ) < C_x4 := by dsimp only [C_x4]; norm_num
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
    have hcancel : C_x4 * ((1 : ℝ) / C_x4 * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)) =
        ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2) := by
      field_simp [ne_of_gt hCpos]
    linarith
  have hx4_nn : 0 ≤ x4n := by
    have : 0 ≤ (Real.exp (-18) / 32) * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2) := by positivity
    linarith
  have hterm2 : 2 * ((n : ℝ) / S) * Psum ≤ (1 / 1000 : ℝ) * x4n := by
    have h1 : 2 * ((n : ℝ) / S) * Psum ≤
        2 * (900 * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)) * (100 / L ^ (1 / 3 : ℝ)) := by
      gcongr
    have h2 : 100 / L ^ (1 / 3 : ℝ) ≤ 100 / A :=
      div_le_div_of_nonneg_left (by norm_num) hA_pos hL13
    have h3 : 2 * (900 * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)) * (100 / L ^ (1 / 3 : ℝ)) ≤
        (180000 / A) * (C_x4 * x4n) := by
      have h3a : 2 * (900 * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)) * (100 / L ^ (1 / 3 : ℝ)) ≤
          2 * (900 * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)) * (100 / A) := by gcongr
      have h3b : 2 * (900 * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)) * (100 / A) =
          (180000 / A) * (((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)) := by ring
      rw [h3b] at h3a
      exact le_trans h3a (mul_le_mul_of_nonneg_left hbase_le (by positivity))
    have h4 : (180000 / A) * C_x4 ≤ 1 / 1000 := by
      rw [hA]; dsimp only [C_x4]; norm_num
    have h5 : (180000 / A) * (C_x4 * x4n) ≤ (1 / 1000 : ℝ) * x4n := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h4 hx4_nn
    linarith
  let B_big : ℝ := (1000000 : ℝ) * 1000000 * 1000
  have hn16_ge : B_big * L ^ 2 ≤ (n : ℝ) ^ (1 / 6 : ℝ) := by
    rw [Real.rpow_def_of_pos hn_pos]
    have hcube : (L * (1 / 6 : ℝ)) ^ 3 / 6 ≤ Real.exp (L * (1 / 6 : ℝ)) := by
      have := Real.pow_div_factorial_le_exp (L * (1 / 6 : ℝ)) (by positivity) 3
      norm_num [Nat.factorial] at this
      exact this
    have hcoeff : B_big ≤ L / 1296 := by
      have : B_big * 1296 ≤ A := by rw [hA]; dsimp only [B_big]; norm_num
      linarith
    have hmul : B_big * L ^ 2 ≤ (L * (1 / 6 : ℝ)) ^ 3 / 6 := by
      have : (L * (1 / 6 : ℝ)) ^ 3 / 6 = (L / 1296) * L ^ 2 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg L)
    linarith
  have hn56_le : (n : ℝ) ^ (5 / 6 : ℝ) ≤ (1 / B_big) * ((n : ℝ) / L ^ 2) := by
    have hsplit : (n : ℝ) = (n : ℝ) ^ (5 / 6 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    have h1 : (n : ℝ) ^ (5 / 6 : ℝ) * (B_big * L ^ 2) ≤ (n : ℝ) := by
      calc (n : ℝ) ^ (5 / 6 : ℝ) * (B_big * L ^ 2)
          ≤ (n : ℝ) ^ (5 / 6 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left hn16_ge (by positivity)
        _ = (n : ℝ) := hsplit.symm
    have hBpos : 0 < B_big := by dsimp only [B_big]; norm_num
    have hden : 0 < B_big * L ^ 2 := by positivity
    have h2 : (n : ℝ) ^ (5 / 6 : ℝ) ≤ (n : ℝ) / (B_big * L ^ 2) := (le_div_iff₀ hden).mpr h1
    have h3 : (n : ℝ) / (B_big * L ^ 2) = (1 / B_big) * ((n : ℝ) / L ^ 2) := by ring
    linarith
  have hn_div_T : (n : ℝ) / (T : ℝ) ≤ (n : ℝ) ^ (5 / 6 : ℝ) := by
    have h1 : (n : ℝ) / (T : ℝ) ≤ (n : ℝ) / (n : ℝ) ^ (1 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hn_pos) (Real.rpow_pos_of_pos hn_pos _) hT_ge_n15
    have h2 : (n : ℝ) / (n : ℝ) ^ (1 / 5 : ℝ) = (n : ℝ) ^ (4 / 5 : ℝ) := by
      rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hn_pos _)), ← Real.rpow_add hn_pos]; norm_num
    have h3 : (n : ℝ) ^ (4 / 5 : ℝ) ≤ (n : ℝ) ^ (5 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    linarith
  have hsqrt_z4 : (Nat.sqrt n : ℝ) * (z : ℝ) ^ 4 ≤ (n : ℝ) ^ (5 / 6 : ℝ) := by
    have h1 : (Nat.sqrt n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      have hsq : ((Nat.sqrt n : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
      calc (Nat.sqrt n : ℝ) = (((Nat.sqrt n : ℝ)) ^ 2) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hsq (by positivity)
    have h2 : (z : ℝ) ^ 4 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      calc (z : ℝ) ^ 4 ≤ ((n : ℝ) ^ (1 / 12 : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hz_le_rpow 4
        _ = (n : ℝ) ^ (1 / 3 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have h3 : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) ^ (5 / 6 : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    calc (Nat.sqrt n : ℝ) * (z : ℝ) ^ 4 ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (n : ℝ) ^ (5 / 6 : ℝ) := h3
  have hterm13 : 4 * ((n : ℝ) / (T : ℝ)) + 2 * (Nat.sqrt n : ℝ) * (z : ℝ) ^ 4 ≤ (1 / 1000 : ℝ) * x4n := by
    have h1 : 4 * ((n : ℝ) / (T : ℝ)) + 2 * (Nat.sqrt n : ℝ) * (z : ℝ) ^ 4 ≤ 6 * (n : ℝ) ^ (5 / 6 : ℝ) := by linarith
    have h2 : (n : ℝ) / L ^ 2 ≤ ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2) :=
      le_mul_of_one_le_left (by positivity) htot_ge1
    have h3 : 6 * (n : ℝ) ^ (5 / 6 : ℝ) ≤ (6 / B_big) * (C_x4 * x4n) := by
      calc 6 * (n : ℝ) ^ (5 / 6 : ℝ)
          ≤ 6 * ((1 / B_big) * ((n : ℝ) / L ^ 2)) := by linarith
        _ = (6 / B_big) * ((n : ℝ) / L ^ 2) := by ring
        _ ≤ (6 / B_big) * (((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (6 / B_big) * (C_x4 * x4n) := mul_le_mul_of_nonneg_left hbase_le (by positivity)
    have h4 : (6 / B_big) * C_x4 ≤ 1 / 1000 := by dsimp only [B_big, C_x4]; norm_num
    have h5 : (6 / B_big) * (C_x4 * x4n) ≤ (1 / 1000 : ℝ) * x4n := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h4 hx4_nn
    linarith
  linarith

theorem main_theorem :
    have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ));
    have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2);
    have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)};
    have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ));
    have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5};
    have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊Real.exp (Real.log (↑x6 : ℝ) / (2 : ℝ) - (2 : ℝ) * Real.log (↑x6 : ℝ) ^ (2 / 3 : ℝ))⌋₊;
    ∃ (x7 : ℕ), ∀ (x8 : ℕ), x7 ≤ x8 → Even x8 → (↑{x11 ∈ x5 x8 | x6 x8 < x11.minFac ∨ x6 x8 < (x8 - x11).minFac}.card : ℝ) ≤ (1 / 500 : ℝ) * x4 x8 := by
  intro x1 x2 x3 x4 x5 x6
  -- Asymptotic threshold: pick `N0` large enough so `(log n)^(1/3) ≥ C`
  have hlog_tendsto : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_ge_ev : ∀ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, C ≤ Real.log (n : ℝ) :=
    fun C => hlog_tendsto.eventually (Filter.eventually_ge_atTop C)
  -- `Real.exp (L / 100) ≥ L^4` eventually, etc., by explicit `L ≥ L0`
  let A : ℝ := (1000000 : ℝ) * 1000000 * 1000000 * 100
  let L0 : ℝ := A ^ 3
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (hlog_ge_ev L0)
  refine ⟨max N1 10000, fun n hn heven => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn10k : 10000 ≤ n := le_trans (le_max_right _ _) hn
  have hL : L0 ≤ Real.log (n : ℝ) := hN1 n hn1
  set L : ℝ := Real.log (n : ℝ)
  have hA_ge : (1000 : ℝ) ≤ A := by dsimp only [A]; norm_num
  have hL_ge_A : A ≤ L := by
    dsimp only [L0] at hL
    have : A ≤ A ^ 3 := by nlinarith
    linarith
  have hL_pos : 0 < L := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  -- Key powers of `L`
  have hL13 : A ≤ L ^ (1 / 3 : ℝ) := by
    have h1 : A ^ (3 : ℝ) ≤ L := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact hL
    calc A = (A ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ L ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hL23_eq : L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) = L := by
    rw [← Real.rpow_add hL_pos]; norm_num
  have hL23_le : 2 * L ^ (2 / 3 : ℝ) ≤ L / 10 := by
    have : 20 * L ^ (2 / 3 : ℝ) ≤ L ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [show L ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ) = L by linarith [hL23_eq, mul_comm (L ^ (2 / 3 : ℝ)) (L ^ (1 / 3 : ℝ))]]
  -- Bounds on `T = x6 n` and `z = ⌊n^(1/12)⌋₊`
  set T : ℕ := x6 n
  set z : ℕ := ⌊(n : ℝ) ^ (1 / 12 : ℝ)⌋₊
  have hT_exp_ge : Real.exp (L / 4) ≤ Real.exp (L / 2 - 2 * L ^ (2 / 3 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hT_ge_rpow : (n : ℝ) ^ (1 / 4 : ℝ) ≤ Real.exp (L / 2 - 2 * L ^ (2 / 3 : ℝ)) := by
    have : (n : ℝ) ^ (1 / 4 : ℝ) = Real.exp (L / 4) := by
      rw [Real.rpow_def_of_pos hn_pos]; congr 1; ring
    linarith
  have hT_ge_exp : Real.exp (L / 2 - 2 * L ^ (2 / 3 : ℝ)) - 1 < (T : ℝ) := by
    have := Nat.lt_floor_add_one (Real.exp (L / 2 - 2 * L ^ (2 / 3 : ℝ)))
    dsimp only [T, x6]; linarith
  have hT_ge_n15 : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (T : ℝ) := by
    have h1 : 2 * (n : ℝ) ^ (1 / 5 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      have hratio : (n : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ) := by
        rw [← Real.rpow_add hn_pos]; congr 1; norm_num
      have hge2 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
        rw [Real.rpow_def_of_pos hn_pos]
        have h1 : 1 ≤ L * (1 / 20 : ℝ) := by dsimp only [L0] at hL; linarith
        have := Real.add_one_le_exp (L * (1 / 20 : ℝ))
        linarith
      rw [hratio]; nlinarith [Real.rpow_nonneg (le_of_lt hn_pos) (1 / 5 : ℝ)]
    have hge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by positivity)
    linarith
  have hT_ge2 : 2 ≤ T := by
    have h1 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
      rw [Real.rpow_def_of_pos hn_pos]
      have h1 : 1 ≤ L * (1 / 5 : ℝ) := by dsimp only [L0] at hL; linarith
      linarith [Real.add_one_le_exp (L * (1 / 5 : ℝ))]
    have : (2 : ℝ) ≤ (T : ℝ) := le_trans h1 hT_ge_n15
    exact_mod_cast this
  have hlogT_ge : L / 5 ≤ Real.log (T : ℝ) := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hn_pos _) hT_ge_n15
    rw [Real.log_rpow hn_pos] at h1
    linarith
  have hz_le_rpow : (z : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := Nat.floor_le (by positivity)
  have hz_ge_rpow : (n : ℝ) ^ (1 / 12 : ℝ) - 1 < (z : ℝ) := by
    have := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 12 : ℝ)); linarith
  have hz_ge_half : (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) ≤ (z : ℝ) := by
    have hge2 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := by
      rw [Real.rpow_def_of_pos hn_pos]
      have : 1 ≤ L * (1 / 12 : ℝ) := by dsimp only [L0] at hL; linarith
      linarith [Real.add_one_le_exp (L * (1 / 12 : ℝ))]
    linarith
  have hz_ge1 : 1 ≤ z := by
    have : (1 : ℝ) ≤ (z : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := by
        rw [Real.rpow_def_of_pos hn_pos]
        have : 1 ≤ L * (1 / 12 : ℝ) := by dsimp only [L0] at hL; linarith
        linarith [Real.add_one_le_exp (L * (1 / 12 : ℝ))]
      linarith
    exact_mod_cast this
  have hz_lt_T : z < T := by
    have h1 : (n : ℝ) ^ (1 / 12 : ℝ) < (n : ℝ) ^ (1 / 5 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) (by norm_num)
    have : (z : ℝ) < (T : ℝ) := lt_of_le_of_lt hz_le_rpow (lt_of_lt_of_le h1 hT_ge_n15)
    exact_mod_cast this
  have hz_le_cbrt : z ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num))
  -- Step 1: Symmetry of `x5 n` under `u ↦ n - u`
  let Bad := (x5 n).filter (fun u => T < u.minFac ∨ T < (n - u).minFac)
  let Bad1 := (x5 n).filter (fun u => T < u.minFac)
  have hsymm : Bad.card ≤ 2 * Bad1.card := by
    let Bad2 := (x5 n).filter (fun u => T < (n - u).minFac)
    have hsub : Bad ⊆ Bad1 ∪ Bad2 := by
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      rw [Finset.mem_union]
      rcases hu'.2 with h1 | h2
      · left; exact Finset.mem_filter.mpr ⟨hu'.1, h1⟩
      · right; exact Finset.mem_filter.mpr ⟨hu'.1, h2⟩
    have hcard2 : Bad2.card = Bad1.card := by
      apply Finset.card_bij (fun u _ => n - u)
      · intro u hu
        have hu' := Finset.mem_filter.mp hu
        have hu5 := Finset.mem_filter.mp hu'.1
        have hu1 := (Finset.mem_filter.mp hu5.1).1
        have hle_n : u ≤ n := by
          have := (Finset.mem_Icc.mp hu1).2
          have := Nat.div_mul_le_self (2 * n) 3
          omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hu5.2, ?_⟩, hu'.2⟩
        rw [Nat.sub_sub_self hle_n]
        exact hu5.1
      · intro u1 hu1 u2 hu2 heq
        have hle1 : u1 ≤ n := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu1).1).1).1).2
          have := Nat.div_mul_le_self (2 * n) 3; omega
        have hle2 : u2 ≤ n := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu2).1).1).1).2
          have := Nat.div_mul_le_self (2 * n) 3; omega
        omega
      · intro v hv
        have hv' := Finset.mem_filter.mp hv
        have hv5 := Finset.mem_filter.mp hv'.1
        have hle_n : v ≤ n := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv5.1).1).2
          have := Nat.div_mul_le_self (2 * n) 3; omega
        refine ⟨n - v, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hv5.2, ?_⟩, ?_⟩, Nat.sub_sub_self hle_n⟩
        · rw [Nat.sub_sub_self hle_n]; exact hv5.1
        · rw [Nat.sub_sub_self hle_n]; exact hv'.2
    calc Bad.card ≤ (Bad1 ∪ Bad2).card := Finset.card_le_card hsub
      _ ≤ Bad1.card + Bad2.card := Finset.card_union_le _ _
      _ = 2 * Bad1.card := by rw [hcard2]; ring
  -- Step 2: Partition `Bad1` by `p = u.minFac` into `p ∣ n` and `¬ p ∣ n`
  let P_all := (Finset.Ioc T (Nat.sqrt n)).filter Nat.Prime
  let Bad_dvd := Bad1.filter (fun u => u.minFac ∣ n)
  let Bad_ndvd := Bad1.filter (fun u => ¬ u.minFac ∣ n)
  have hBad1_split : Bad1.card = Bad_dvd.card + Bad_ndvd.card := by
    dsimp only [Bad_dvd, Bad_ndvd]
    exact (Finset.card_filter_add_card_filter_not (s := Bad1) (p := fun u => u.minFac ∣ n)).symm
  -- Every `u ∈ Bad1` has `u.minFac ∈ P_all`
  have hminFac_mem : ∀ u ∈ Bad1, u.minFac ∈ P_all := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    have hu3 := (Finset.mem_filter.mp hu'.1).1
    have hu3' := Finset.mem_filter.mp hu3
    have hu_le : u ≤ n := by
      have := (Finset.mem_Icc.mp hu3'.1).2
      have := Nat.div_mul_le_self (2 * n) 3; omega
    have hu_pos : 0 < u := by
      have := (Finset.mem_Icc.mp hu3'.1).1; omega
    have hpP : Nat.Prime u.minFac := hu3'.2.2.1
    have hqP : Nat.Prime (u / u.minFac) := hu3'.2.2.2
    have hp_le_q : u.minFac ≤ u / u.minFac := by
      have hq_dvd : u / u.minFac ∣ u := Nat.div_dvd_of_dvd (Nat.minFac_dvd u)
      exact Nat.minFac_le_of_dvd hqP.two_le hq_dvd
    have hpsq : u.minFac * u.minFac ≤ n := by
      have hmul : u.minFac * (u / u.minFac) = u := Nat.mul_div_cancel' (Nat.minFac_dvd u)
      calc u.minFac * u.minFac ≤ u.minFac * (u / u.minFac) := Nat.mul_le_mul_left _ hp_le_q
        _ = u := hmul
        _ ≤ n := hu_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hu'.2, Nat.le_sqrt.mpr hpsq⟩, hpP⟩
  -- Bound `Bad_dvd.card ≤ 2 * (n / T)`
  have hBad_dvd_le : (Bad_dvd.card : ℝ) ≤ 2 * ((n : ℝ) / (T : ℝ)) := by
    let P_dvd := n.primeFactors.filter (fun p => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < p)
    have hmaps : ∀ u ∈ Bad_dvd, u.minFac ∈ P_dvd := by
      intro u hu
      have hu1 := (Finset.mem_filter.mp hu).1
      have hdvd := (Finset.mem_filter.mp hu).2
      have hu3' := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu1).1).1
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hu3'.2.2.1, hdvd, by omega⟩, hu3'.2.1⟩
    have hcard : Bad_dvd.card ≤ ∑ p ∈ P_dvd, (Bad_dvd.filter (fun u => u.minFac = p)).card := by
      have h1 := Finset.card_eq_sum_card_fiberwise hmaps
      omega
    have hfiber : ∀ p ∈ P_dvd, (Bad_dvd.filter (fun u => u.minFac = p)).card ≤ n / T := by
      intro p hp
      have hsub : (Bad_dvd.filter (fun u => u.minFac = p)).image (fun u => u / p) ⊆ Finset.Icc 1 (n / T) := by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨u, hu, rfl⟩
        have hu_dvd := (Finset.mem_filter.mp hu).1
        have hu_p := (Finset.mem_filter.mp hu).2
        have hu1 := (Finset.mem_filter.mp hu_dvd).1
        have hp_gt_T : T < p := by rw [← hu_p]; exact (Finset.mem_filter.mp hu1).2
        have hu3' := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu1).1).1
        have hu_le : u ≤ n := by
          have := (Finset.mem_Icc.mp hu3'.1).2; have := Nat.div_mul_le_self (2 * n) 3; omega
        have hq_pos : 1 ≤ u / p := by
          have := hu3'.2.2.2.pos; rwa [hu_p] at this
        have hq_le : u / p ≤ n / T := by
          calc u / p ≤ n / p := Nat.div_le_div_right hu_le
            _ ≤ n / T := Nat.div_le_div_left (le_of_lt hp_gt_T) (by omega)
        exact Finset.mem_Icc.mpr ⟨hq_pos, hq_le⟩
      have hinj : Set.InjOn (fun u => u / p) ((Bad_dvd.filter (fun u => u.minFac = p)) : Set ℕ) := by
        intro u1 hu1 u2 hu2 heq
        have h1 : p ∣ u1 := (Finset.mem_filter.mp hu1).2 ▸ Nat.minFac_dvd u1
        have h2 : p ∣ u2 := (Finset.mem_filter.mp hu2).2 ▸ Nat.minFac_dvd u2
        dsimp only at heq
        rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
      calc (Bad_dvd.filter (fun u => u.minFac = p)).card
          = ((Bad_dvd.filter (fun u => u.minFac = p)).image (fun u => u / p)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Icc 1 (n / T)).card := Finset.card_le_card hsub
        _ = n / T := by rw [Nat.card_Icc]; simp
    have htot : Bad_dvd.card ≤ 2 * (n / T) := by
      calc Bad_dvd.card ≤ ∑ p ∈ P_dvd, (Bad_dvd.filter (fun u => u.minFac = p)).card := hcard
        _ ≤ ∑ _p ∈ P_dvd, (n / T) := Finset.sum_le_sum hfiber
        _ = P_dvd.card * (n / T) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 * (n / T) := Nat.mul_le_mul_right _ (card_primeFactors_gt_cbrt_le_two n (by omega))
    have hdiv_le : ((n / T : ℕ) : ℝ) ≤ (n : ℝ) / (T : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < T))]
      exact_mod_cast Nat.div_mul_le_self n T
    have htotR : (Bad_dvd.card : ℝ) ≤ 2 * ((n / T : ℕ) : ℝ) := by exact_mod_cast htot
    linarith
  -- Step 3: Bound `Bad_ndvd.card` using `selberg_upper_bound` for each `p ∈ P_all`
  let D := (Finset.Icc 1 z).filter Squarefree
  let S := ∑ d ∈ D, hSel n d
  have h1D : 1 ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hz_ge1⟩, squarefree_one⟩
  have hS_pos : 0 < S := Finset.sum_pos (fun _ _ => hSel_pos heven) ⟨1, h1D⟩
  have hBad_ndvd_le : (Bad_ndvd.card : ℝ) ≤
      ((n : ℝ) / S) * (∑ p ∈ P_all, (1 : ℝ) / (p : ℝ)) + (Nat.sqrt n : ℝ) * (z : ℝ) ^ 4 := by
    have hmaps : ∀ u ∈ Bad_ndvd, u.minFac ∈ P_all :=
      fun u hu => hminFac_mem u (Finset.mem_filter.mp hu).1
    have hpart : (Bad_ndvd.card : ℝ) =
        ∑ p ∈ P_all, ((Bad_ndvd.filter (fun u => u.minFac = p)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
      apply Finset.sum_congr rfl; intro p _; rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    rw [hpart]
    have hfiber : ∀ p ∈ P_all, ((Bad_ndvd.filter (fun u => u.minFac = p)).card : ℝ) ≤
        ((n : ℝ) / S) * ((1 : ℝ) / (p : ℝ)) + (z : ℝ) ^ 4 := by
      intro p hp
      have hpI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
      have hpP := (Finset.mem_filter.mp hp).2
      have hzp : z < p := lt_trans hz_lt_T hpI.1
      let X := n / p
      have hsub : (Bad_ndvd.filter (fun u => u.minFac = p)).image (fun u => u / p) ⊆
          (Finset.Icc 1 X).filter (fun q =>
            ∀ r ∈ (Finset.Icc 2 z).filter Nat.Prime,
              ¬ (r : ℤ) ∣ (q : ℤ) * ((n : ℤ) - (p : ℤ) * (q : ℤ))) := by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨u, hu, rfl⟩
        have hu_nd := (Finset.mem_filter.mp hu).1
        have hu_p := (Finset.mem_filter.mp hu).2
        have hu1 := (Finset.mem_filter.mp hu_nd).1
        have hu5 := Finset.mem_filter.mp (Finset.mem_filter.mp hu1).1
        have hu3 := Finset.mem_filter.mp hu5.1
        have hnu3 := Finset.mem_filter.mp hu5.2
        have hu_le : u ≤ n := by
          have := (Finset.mem_Icc.mp hu3.1).2; have := Nat.div_mul_le_self (2 * n) 3; omega
        have hpq_eq : p * (u / p) = u := by
          have := Nat.mul_div_cancel' (Nat.minFac_dvd u); rwa [hu_p] at this
        have hqP : Nat.Prime (u / p) := by rw [← hu_p]; exact hu3.2.2.2
        have hq_ge_p : p ≤ u / p := by
          rw [← hu_p]; exact Nat.minFac_le_of_dvd hu3.2.2.2.two_le (Nat.div_dvd_of_dvd (Nat.minFac_dvd u))
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqP.pos, Nat.div_le_div_right hu_le⟩, ?_⟩
        intro r hr hr_dvd
        have hrI := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
        have hrP := (Finset.mem_filter.mp hr).2
        have hrZ : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hrP
        rcases hrZ.dvd_or_dvd hr_dvd with h1 | h2
        · have hrq : r ∣ u / p := Int.natCast_dvd_natCast.mp h1
          have heq := (Nat.prime_dvd_prime_iff_eq hrP hqP).mp hrq
          omega
        · have hcast : (n : ℤ) - (p : ℤ) * ((u / p : ℕ) : ℤ) = ((n - u : ℕ) : ℤ) := by
            have h1 : ((p * (u / p) : ℕ) : ℤ) = (u : ℤ) := by exact_mod_cast hpq_eq
            rw [Nat.cast_sub hu_le, ← h1]; push_cast; rfl
          rw [hcast] at h2
          have hrnu : r ∣ n - u := Int.natCast_dvd_natCast.mp h2
          have hmin_le : (n - u).minFac ≤ r := Nat.minFac_le_of_dvd hrP.two_le hrnu
          have hmin_gt : ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < (n - u).minFac := hnu3.2.1
          omega
      have hinj : Set.InjOn (fun u => u / p) ((Bad_ndvd.filter (fun u => u.minFac = p)) : Set ℕ) := by
        intro u1 hu1 u2 hu2 heq
        have h1 : p ∣ u1 := (Finset.mem_filter.mp hu1).2 ▸ Nat.minFac_dvd u1
        have h2 : p ∣ u2 := (Finset.mem_filter.mp hu2).2 ▸ Nat.minFac_dvd u2
        dsimp only at heq
        rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
      have hcard_le : ((Bad_ndvd.filter (fun u => u.minFac = p)).card : ℝ) ≤
          (((Finset.Icc 1 X).filter (fun q : ℕ =>
            ∀ r ∈ (Finset.Icc 2 z).filter Nat.Prime,
              ¬ (r : ℤ) ∣ (q : ℤ) * ((n : ℤ) - (p : ℤ) * (q : ℤ)))).card : ℝ) := by
        rw [← Finset.card_image_of_injOn hinj]
        exact_mod_cast Finset.card_le_card hsub
      have hsel := selberg_upper_bound (n := n) (p := p) (z := z) (X := X) heven hpP hz_ge1 hzp
      have hX_le : (X : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hpP.pos)]
        exact_mod_cast Nat.div_mul_le_self n p
      have hX_div : (X : ℝ) / S ≤ ((n : ℝ) / S) * ((1 : ℝ) / (p : ℝ)) := by
        have h1 : (X : ℝ) / S ≤ ((n : ℝ) / (p : ℝ)) / S := div_le_div_of_nonneg_right hX_le (le_of_lt hS_pos)
        have h2 : ((n : ℝ) / (p : ℝ)) / S = ((n : ℝ) / S) * ((1 : ℝ) / (p : ℝ)) := by ring
        linarith
      linarith
    calc ∑ p ∈ P_all, ((Bad_ndvd.filter (fun u => u.minFac = p)).card : ℝ)
        ≤ ∑ p ∈ P_all, (((n : ℝ) / S) * ((1 : ℝ) / (p : ℝ)) + (z : ℝ) ^ 4) := Finset.sum_le_sum hfiber
      _ = ((n : ℝ) / S) * (∑ p ∈ P_all, (1 : ℝ) / (p : ℝ)) + (P_all.card : ℝ) * (z : ℝ) ^ 4 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) / S) * (∑ p ∈ P_all, (1 : ℝ) / (p : ℝ)) + (Nat.sqrt n : ℝ) * (z : ℝ) ^ 4 := by
          gcongr
          have hcard : P_all.card ≤ Nat.sqrt n := by
            have h1 : P_all.card ≤ (Finset.Ioc T (Nat.sqrt n)).card := Finset.card_le_card (Finset.filter_subset _ _)
            rw [Nat.card_Ioc] at h1; omega
          exact_mod_cast hcard
  -- Step 4: Dyadic bound on `∑_{p ∈ P_all} 1/p ≤ 100 / L^(1/3)`
  have hdyadic : ∑ p ∈ P_all, (1 : ℝ) / (p : ℝ) ≤ 100 / L ^ (1 / 3 : ℝ) :=
    dyadic_tail_bound hn10k hT_ge2 (by linarith) hT_ge_exp hlogT_ge
  -- Step 5: Lower bound on `S` and `x4 n`
  have hS_ge : ((n.totient : ℝ) / (n : ℝ)) * (L / 30) ^ 2 ≤ S := by
    have hSb := S_lower_bound (n := n) (z := z) (by omega) heven
    have hlogM : L / 30 ≤ Real.log ((Nat.sqrt z + 1 : ℕ) : ℝ) := by
      have hM_ge : (z : ℝ) ^ (1 / 2 : ℝ) ≤ ((Nat.sqrt z + 1 : ℕ) : ℝ) := by
        have hlt : z < (Nat.sqrt z + 1) * (Nat.sqrt z + 1) := Nat.lt_succ_sqrt z
        have hltR : (z : ℝ) ≤ ((Nat.sqrt z + 1 : ℕ) : ℝ) ^ 2 := by
          rw [sq]; exact_mod_cast le_of_lt hlt
        calc (z : ℝ) ^ (1 / 2 : ℝ) ≤ (((Nat.sqrt z + 1 : ℕ) : ℝ) ^ 2) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (by positivity) hltR (by positivity)
          _ = ((Nat.sqrt z + 1 : ℕ) : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have hlog1 := Real.log_le_log (Real.rpow_pos_of_pos (by exact_mod_cast hz_ge1) _) hM_ge
      rw [Real.log_rpow (by exact_mod_cast hz_ge1)] at hlog1
      have hlogz : L / 15 ≤ Real.log (z : ℝ) := by
        have h1 : (n : ℝ) ^ (1 / 15 : ℝ) ≤ (z : ℝ) := by
          have h2 : (n : ℝ) ^ (1 / 15 : ℝ) ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) := by
            have hratio : (n : ℝ) ^ (1 / 12 : ℝ) = (n : ℝ) ^ (1 / 15 : ℝ) * (n : ℝ) ^ (1 / 60 : ℝ) := by
              rw [← Real.rpow_add hn_pos]; congr 1; norm_num
            have hge2 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 60 : ℝ) := by
              rw [Real.rpow_def_of_pos hn_pos]
              have : 1 ≤ L * (1 / 60 : ℝ) := by dsimp only [L0] at hL; linarith
              linarith [Real.add_one_le_exp (L * (1 / 60 : ℝ))]
            rw [hratio]; nlinarith [Real.rpow_nonneg (le_of_lt hn_pos) (1 / 15 : ℝ)]
          exact le_trans h2 hz_ge_half
        have h2 := Real.log_le_log (Real.rpow_pos_of_pos hn_pos _) h1
        rw [Real.log_rpow hn_pos] at h2; linarith
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlogM 2) (by positivity)) hSb
  have hx4_ge : (Real.exp (-18) / 32) * ((n : ℝ) / (n.totient : ℝ)) * ((n : ℝ) / L ^ 2) ≤ x4 n :=
    x4_lower_bound hn10k heven
  -- Step 6: Combine all bounds!
  have hBad_le : (Bad.card : ℝ) ≤
      4 * ((n : ℝ) / (T : ℝ)) +
      2 * ((n : ℝ) / S) * (∑ p ∈ P_all, (1 : ℝ) / (p : ℝ)) +
      2 * (Nat.sqrt n : ℝ) * (z : ℝ) ^ 4 := by
    have h1 : (Bad.card : ℝ) ≤ 2 * ((Bad_dvd.card : ℝ) + (Bad_ndvd.card : ℝ)) := by
      exact_mod_cast (by omega : Bad.card ≤ 2 * (Bad_dvd.card + Bad_ndvd.card))
    linarith
  have hcomb := final_combine_bound hn10k rfl hL_ge_A hL13 hT_ge_n15 hz_le_rpow hS_ge
    (Finset.sum_nonneg (fun _ _ => by positivity)) hdyadic hx4_ge
  exact le_trans hBad_le hcomb

end Conjectures.Cuts.Taskd4c2c458Proof

theorem Conjectures.Cuts.Taskd4c2c458d1b6958628c99f53 : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊Real.exp (Real.log (↑x6 : ℝ) / (2 : ℝ) - (2 : ℝ) * Real.log (↑x6 : ℝ) ^ (2 / 3 : ℝ))⌋₊; ∃ (x7 : ℕ), ∀ (x8 : ℕ), x7 ≤ x8 → Even x8 → (↑{x11 ∈ x5 x8 | x6 x8 < x11.minFac ∨ x6 x8 < (x8 - x11).minFac}.card : ℝ) ≤ (1 / 500 : ℝ) * x4 x8) :=
  Conjectures.Cuts.Taskd4c2c458Proof.main_theorem

