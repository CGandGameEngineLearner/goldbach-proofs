import Mathlib

open scoped BigOperators

namespace Conjectures.Cuts.Task99950cab5c8977334dbea5e5_aux

section

variable (f : ℕ → ℝ) (N q : ℕ)

private lemma residue_indicator (hq : 0 < q) (n n' : ℕ) :
    (∑ r ∈ Finset.range q, (if n % q = r then f n else 0) * (if n' % q = r then f n' else 0))
      = if n % q = n' % q then f n * f n' else 0 := by
  by_cases h : n % q = n' % q
  · rw [if_pos h, Finset.sum_eq_single (n % q)]
    · rw [if_pos rfl, if_pos h.symm]
    · intro r _ hr
      rw [if_neg hr.symm, zero_mul]
    · intro hmem
      exact absurd (Nat.mod_lt n hq) (Finset.mem_range.not.mp hmem)
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun r _ => ?_)
    by_cases h1 : n % q = r
    · have h2 : n' % q ≠ r := fun h2 => h (h1.trans h2.symm)
      rw [if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private lemma expand_sq (hq : 0 < q) :
    (∑ r ∈ Finset.range q, (∑ n ∈ Finset.range N with n % q = r, f n) ^ (2 : ℕ))
      = ∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
          if n % q = n' % q then f n * f n' else 0 := by
  have hfilter : ∀ r : ℕ,
      (∑ n ∈ Finset.range N with n % q = r, f n)
        = ∑ n ∈ Finset.range N, if n % q = r then f n else 0 :=
    fun r => by rw [Finset.sum_filter]
  simp_rw [hfilter, sq]
  have hmul : ∀ r : ℕ,
      (∑ n ∈ Finset.range N, if n % q = r then f n else 0)
        * (∑ n' ∈ Finset.range N, if n' % q = r then f n' else 0)
      = ∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
          (if n % q = r then f n else 0) * (if n' % q = r then f n' else 0) := by
    intro r
    rw [Finset.sum_mul_sum]
  simp_rw [hmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n' _ => ?_)
  exact residue_indicator f q hq n n'

private lemma indicator_split (n n' : ℕ) :
    (if n % q = n' % q then f n * f n' else 0)
      = (if n = n' then f n * f n' else 0)
        + (if n % q = n' % q ∧ n < n' then f n * f n' else 0)
        + (if n % q = n' % q ∧ n' < n then f n * f n' else 0) := by
  rcases Nat.lt_trichotomy n n' with h | rfl | h
  · by_cases hm : n % q = n' % q
    · simp [hm, h, h.ne, h.ne', not_lt_of_ge (le_of_lt h)]
    · simp [hm, h, h.ne, h.ne', not_lt_of_ge (le_of_lt h)]
  · simp
  · by_cases hm : n % q = n' % q
    · simp [hm, h, h.ne, h.ne', not_lt_of_ge (le_of_lt h)]
    · simp [hm, h, h.ne, h.ne', not_lt_of_ge (le_of_lt h)]

private lemma diag_sum :
    (∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N, if n = n' then f n * f n' else 0)
      = ∑ n ∈ Finset.range N, f n ^ (2 : ℕ) := by
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.sum_ite_eq, if_pos hn, sq]

private lemma upper_lower_point (a b : ℕ) :
    (if a % q = b % q ∧ b < a then f a * f b else 0)
      = if b % q = a % q ∧ b < a then f b * f a else 0 := by
  by_cases hm : a % q = b % q
  · by_cases hlt : b < a
    · simp [hm, hlt, mul_comm]
    · simp [hm, hlt]
  · have hm' : b % q ≠ a % q := fun h => hm h.symm
    simp [hm, hm']

private lemma upper_eq_lower :
    (∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
        if n % q = n' % q ∧ n' < n then f n * f n' else 0)
      = ∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
          if n % q = n' % q ∧ n < n' then f n * f n' else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun n' _ => ?_))
  exact upper_lower_point f q n' n

private lemma dvd_sub (n n' q : ℕ) (hmod : n % q = n' % q) : q ∣ n' - n :=
  Nat.dvd_iff_mod_eq_zero.mpr (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)

private lemma div_mul_sub (n n' q : ℕ) (hmod : n % q = n' % q) :
    q * ((n' - n) / q) = n' - n := by
  rw [mul_comm, Nat.div_mul_cancel (dvd_sub n n' q hmod)]

private lemma shift_reindex (hq : 0 < q) (n : ℕ) :
    (∑ n' ∈ Finset.range N, if n % q = n' % q ∧ n < n' then f n * f n' else 0)
      = ∑ d ∈ Finset.Icc (1 : ℕ) ((N - 1) / q),
          if n + q * d < N then f n * f (n + q * d) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun n' _ => (n' - n) / q) (fun d _ => n + q * d) ?_ ?_ ?_ ?_ ?_
  · intro n' hn'
    obtain ⟨hn'range, hmod, hlt⟩ := Finset.mem_filter.mp hn'
    have hn'N : n' < N := Finset.mem_range.mp hn'range
    have hmul : q * ((n' - n) / q) = n' - n := div_mul_sub n n' q hmod
    have hpos : 0 < n' - n := by omega
    have hd1 : 1 ≤ (n' - n) / q := by
      by_contra h0
      have hz : (n' - n) / q = 0 := Nat.lt_one_iff.mp (not_le.mp h0)
      rw [hz, mul_zero] at hmul
      omega
    have hqle : q ≤ n' - n := by
      calc q = 1 * q := by ring
        _ ≤ (n' - n) / q * q := Nat.mul_le_mul_right q hd1
        _ = n' - n := by rw [mul_comm, hmul]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos hqle hq, ?_⟩, ?_⟩
    · refine (Nat.le_div_iff_mul_le hq).mpr ?_
      have hle : q * ((n' - n) / q) ≤ N - 1 := by omega
      rwa [mul_comm] at hle
    · omega
  · intro d hd
    obtain ⟨hdIcc, hdN⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hdIcc
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdN, ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left]
    · have hqd : 0 < q * d := Nat.mul_pos hq (by omega)
      omega
  · intro n' hn'
    obtain ⟨hn'range, hmod, hlt⟩ := Finset.mem_filter.mp hn'
    have hmul : q * ((n' - n) / q) = n' - n := div_mul_sub n n' q hmod
    omega
  · intro d hd
    obtain ⟨hdIcc, hdN⟩ := Finset.mem_filter.mp hd
    have hqd : (n + q * d - n) / q = d := by
      have : n + q * d - n = q * d := by omega
      rw [this, Nat.mul_div_cancel_left _ hq]
    exact hqd
  · intro n' hn'
    obtain ⟨hn'range, hmod, hlt⟩ := Finset.mem_filter.mp hn'
    have hmul : q * ((n' - n) / q) = n' - n := div_mul_sub n n' q hmod
    have heq : n + q * ((n' - n) / q) = n' := by omega
    rw [heq]

private lemma range_filter_shift (d : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, if n + q * d < N then g n else 0)
      = ∑ n ∈ Finset.range (N - q * d), g n := by
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private lemma lower_eq_shift (hq : 0 < q) :
    (∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
        if n % q = n' % q ∧ n < n' then f n * f n' else 0)
      = ∑ d ∈ Finset.Icc (1 : ℕ) ((N - 1) / q),
          ∑ n ∈ Finset.range (N - q * d), f n * f (n + q * d) := by
  have h1 : (∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
        if n % q = n' % q ∧ n < n' then f n * f n' else 0)
      = ∑ n ∈ Finset.range N, ∑ d ∈ Finset.Icc (1 : ℕ) ((N - 1) / q),
          if n + q * d < N then f n * f (n + q * d) else 0 := by
    refine Finset.sum_congr rfl (fun n _ => shift_reindex f N q hq n)
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  exact range_filter_shift N q d (fun n => f n * f (n + q * d))

theorem main (hq : 0 < q) :
    (∑ r ∈ Finset.range q, (∑ n ∈ Finset.range N with n % q = r, f n) ^ (2 : ℕ))
      = (∑ n ∈ Finset.range N, f n ^ (2 : ℕ))
        + 2 * (∑ d ∈ Finset.Icc (1 : ℕ) ((N - 1) / q),
            ∑ n ∈ Finset.range (N - q * d), f n * f (n + q * d)) := by
  rw [expand_sq f N q hq]
  have hsplit : (∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
        if n % q = n' % q then f n * f n' else 0)
      = (∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N, if n = n' then f n * f n' else 0)
        + (∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
            if n % q = n' % q ∧ n < n' then f n * f n' else 0)
        + (∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N,
            if n % q = n' % q ∧ n' < n then f n * f n' else 0) := by
    simp_rw [indicator_split f q]
    simp only [Finset.sum_add_distrib]
  rw [hsplit, diag_sum f N, upper_eq_lower f N q, lower_eq_shift f N q hq]
  ring

end

end Conjectures.Cuts.Task99950cab5c8977334dbea5e5_aux

theorem Conjectures.Cuts.Task99950cab5c8977334dbea5e5 :
    have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) => ∑ x4 ∈ Finset.range x3, (∑ x5 ∈ Finset.range x2 with x5 % x3 = x4, x1 x5) ^ (2 : ℕ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.Icc (1 : ℕ) ((x3 - (1 : ℕ)) / x4), ∑ x6 ∈ Finset.range (x3 - x4 * x5), x2 x6 * x2 (x6 + x4 * x5); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ), (0 : ℕ) < x5 → x1 x3 x4 x5 = ∑ x7 ∈ Finset.range x4, x3 x7 ^ (2 : ℕ) + (2 : ℝ) * x2 x3 x4 x5 := by
  intro x1 x2 f N q hq
  exact Conjectures.Cuts.Task99950cab5c8977334dbea5e5_aux.main f N q hq
