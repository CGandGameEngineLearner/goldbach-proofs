import Mathlib

noncomputable section
open scoped BigOperators

namespace TSB

def Ez (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def capz (H : ℕ) (x : ℝ) : ℝ := if Ez x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - Ez x‖)

lemma Ez_norm (x : ℝ) : ‖Ez x‖ = 1 := by
  simpa [Ez] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

lemma Ez_add (x y : ℝ) : Ez (x + y) = Ez x * Ez y := by
  unfold Ez
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma Ez_star (x : ℝ) : star (Ez x) = Ez (-x) := by
  have harg : (starRingEnd ℂ) ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)
      = (((2 * Real.pi * (-x) : ℝ)) : ℂ) * Complex.I := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring_nf
  calc star (Ez x) = Complex.exp ((starRingEnd ℂ) ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I)) := by
        rw [Ez]
        exact (Complex.exp_conj _).symm
    _ = Ez (-x) := by rw [harg, Ez]

lemma Ez_pow (m : ℕ) (θ : ℝ) : Ez ((m : ℝ) * θ) = Ez θ ^ m := by
  have harg : (((2 * Real.pi * ((m : ℝ) * θ) : ℝ)) : ℂ) * Complex.I
      = (m : ℂ) * ((((2 * Real.pi * θ : ℝ)) : ℂ) * Complex.I) := by
    push_cast
    ring
  unfold Ez
  rw [harg, Complex.exp_nat_mul]

lemma capz_nonneg (H : ℕ) (x : ℝ) : 0 ≤ capz H x := by
  unfold capz
  by_cases h : Ez x = 1
  · simp [h]
  · rw [if_neg h]
    refine le_min (by positivity) ?_
    have hpos : (0:ℝ) < ‖(1:ℂ) - Ez x‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr (Ne.symm h)
    exact div_nonneg (by norm_num) hpos.le

lemma geom_range_norm_le (q : ℂ) (hq : q ≠ 1) (hqn : ‖q‖ = 1) (a n : ℕ) :
    ‖∑ i ∈ Finset.range n, q ^ (a + i)‖ ≤ 2 / ‖1 - q‖ := by
  have hfac : ∑ i ∈ Finset.range n, q ^ (a + i) = q ^ a * ∑ i ∈ Finset.range n, q ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_add]
  rw [hfac, geom_sum_eq hq n]
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  have hq2 : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hrew : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
    rw [div_eq_div_iff hq1 hq2]
    ring
  rw [hrew, norm_mul, norm_div, norm_pow, hqn, one_pow, one_mul]
  have hnum : ‖(1 : ℂ) - q ^ n‖ ≤ 2 := by
    have h1 : ‖(1:ℂ) - q ^ n‖ ≤ ‖(1:ℂ)‖ + ‖q ^ n‖ := norm_sub_le _ _
    rw [norm_one, norm_pow, hqn, one_pow] at h1
    norm_num at h1
    exact h1
  have hpos : 0 < ‖(1:ℂ) - q‖ := by
    rw [norm_pos_iff]
    exact hq2
  exact (div_le_div_iff_of_pos_right hpos).mpr hnum

lemma geom_Ico_norm_le (H : ℕ) (θ : ℝ) {a b : ℕ} (hab : b - a ≤ H) :
    ‖∑ m ∈ Finset.Ico a b, Ez ((m : ℝ) * θ)‖ ≤ capz H θ := by
  rw [Finset.sum_Ico_eq_sum_range (fun m => Ez ((m : ℝ) * θ)) a b]
  have hterm : ∀ k : ℕ, Ez (((a + k : ℕ) : ℝ) * θ) = Ez θ ^ (a + k) := fun k => Ez_pow (a + k) θ
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  by_cases hq : Ez θ = 1
  · have hval : ∑ k ∈ Finset.range (b - a), Ez θ ^ (a + k) = ((b - a : ℕ) : ℂ) := by
      have hone : ∀ k : ℕ, Ez θ ^ (a + k) = (1 : ℂ) := by
        intro k; rw [hq, one_pow]
      rw [Finset.sum_congr rfl (fun k _ => hone k)]
      simp
    have hcap : capz H θ = (H : ℝ) := by
      unfold capz
      rw [if_pos hq]
    rw [hval, hcap]
    simp only [Complex.norm_natCast]
    exact_mod_cast hab
  · have h2 : ‖∑ k ∈ Finset.range (b - a), Ez θ ^ (a + k)‖ ≤ 2 / ‖1 - Ez θ‖ :=
      geom_range_norm_le (Ez θ) hq (Ez_norm θ) a (b - a)
    have hH : ‖∑ k ∈ Finset.range (b - a), Ez θ ^ (a + k)‖ ≤ (H : ℝ) := by
      have hc : ‖∑ k ∈ Finset.range (b - a), Ez θ ^ (a + k)‖ ≤ ((b - a : ℕ) : ℝ) := by
        calc ‖∑ k ∈ Finset.range (b - a), Ez θ ^ (a + k)‖
            ≤ ∑ k ∈ Finset.range (b - a), ‖Ez θ ^ (a + k)‖ := norm_sum_le _ _
          _ = ∑ k ∈ Finset.range (b - a), (1:ℝ) := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [norm_pow, Ez_norm, one_pow]
          _ = ((b - a : ℕ) : ℝ) := by simp
      exact le_trans hc (Nat.cast_le.mpr hab)
    have hcap : capz H θ = min (H : ℝ) (2 / ‖1 - Ez θ‖) := by
      unfold capz
      rw [if_neg hq]
    rw [hcap]
    exact le_min hH h2

lemma mul_le_iff_lt (m k N M H : ℕ) (hm : m ∈ Finset.Ico M (M + H)) :
    (m * k ≤ N) ↔ m < (if k = 0 then M + H else N / k + 1) := by
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, Nat.mul_zero, Nat.lt_iff_add_one_le]
    simp only [Nat.zero_le, true_iff]
    exact (Finset.mem_Ico.mp hm).2
  · rw [if_neg hk, Nat.lt_succ_iff]
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hk)).symm

def wfun (N : ℕ) (b : ℕ → ℂ) (t : ℝ) (k m : ℕ) : ℂ :=
  if m * k ≤ N then b k * Ez ((m : ℝ) * (k : ℝ) * t) else 0

lemma Ez_mul_star (x y : ℝ) : Ez x * star (Ez y) = Ez (x - y) := by
  rw [Ez_star, ← Ez_add]
  congr 1

lemma wfun_mul (N : ℕ) (b : ℕ → ℂ) (t : ℝ) (k l m : ℕ) :
    wfun N b t k m * star (wfun N b t l m)
      = (b k * star (b l)) *
          (if m * k ≤ N ∧ m * l ≤ N then Ez (((k : ℝ) - (l : ℝ)) * (m : ℝ) * t) else 0) := by
  unfold wfun
  by_cases hk : m * k ≤ N
  · by_cases hl : m * l ≤ N
    · rw [if_pos hk, if_pos hl, if_pos (show m * k ≤ N ∧ m * l ≤ N from ⟨hk, hl⟩), star_mul,
        Ez_star]
      have hargs : ((m : ℝ) * (k : ℝ) * t) + -(((m : ℝ) * (l : ℝ) * t))
          = ((k : ℝ) - (l : ℝ)) * (m : ℝ) * t := by ring
      calc (b k * Ez ((m : ℝ) * (k : ℝ) * t)) * (Ez (-((m : ℝ) * (l : ℝ) * t)) * star (b l))
          = (b k * star (b l)) *
              (Ez ((m : ℝ) * (k : ℝ) * t) * Ez (-((m : ℝ) * (l : ℝ) * t))) := by ring
        _ = (b k * star (b l)) * Ez (((k : ℝ) - (l : ℝ)) * (m : ℝ) * t) := by
            rw [← Ez_add, hargs]
    · rw [if_pos hk, if_neg hl,
        if_neg (show ¬ (m * k ≤ N ∧ m * l ≤ N) from fun h => hl h.2)]
      simp
  · rw [if_neg hk, if_neg (show ¬ (m * k ≤ N ∧ m * l ≤ N) from fun h => hk h.1)]
    simp

lemma pair_sum (N M H : ℕ) (b : ℕ → ℂ) (t : ℝ) (k l : ℕ) :
    ∑ m ∈ Finset.Ico M (M + H), wfun N b t k m * star (wfun N b t l m)
      = (b k * star (b l)) *
          ∑ m ∈ Finset.Ico M (M + H),
            (if m * k ≤ N ∧ m * l ≤ N then Ez (((k : ℝ) - (l : ℝ)) * (m : ℝ) * t) else 0) := by
  rw [Finset.sum_congr rfl (fun m _ => wfun_mul N b t k l m), ← Finset.mul_sum]

lemma prefix_sum_bound (N M H k l : ℕ) (t : ℝ) :
    ‖∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N ∧ m * l ≤ N then Ez (((k : ℝ) - (l : ℝ)) * (m : ℝ) * t) else 0)‖
      ≤ capz H (((k : ℝ) - (l : ℝ)) * t) := by
  classical
  set ck : ℕ := if k = 0 then M + H else N / k + 1 with hck
  set cl : ℕ := if l = 0 then M + H else N / l + 1 with hcl
  have hset : (Finset.Ico M (M + H)).filter (fun m => m * k ≤ N ∧ m * l ≤ N)
      = Finset.Ico M (min (M + H) (min ck cl)) := by
    ext m
    constructor
    · intro hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hmem, h3, h4⟩ := hm
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hmem
      have hmI : m ∈ Finset.Ico M (M + H) := Finset.mem_Ico.mpr ⟨h1, h2⟩
      have hklt : m < ck := by
        rw [hck]
        exact (mul_le_iff_lt m k N M H hmI).mp h3
      have hllt : m < cl := by
        rw [hcl]
        exact (mul_le_iff_lt m l N M H hmI).mp h4
      rw [Finset.mem_Ico]
      exact ⟨h1, lt_min h2 (lt_min hklt hllt)⟩
    · intro hm
      rw [Finset.mem_Ico] at hm
      obtain ⟨h1, h2⟩ := hm
      have hmI : m ∈ Finset.Ico M (M + H) := Finset.mem_Ico.mpr ⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩
      have hklt : m < ck := lt_of_lt_of_le (lt_of_lt_of_le h2 (min_le_right _ _)) (min_le_left _ _)
      have hllt : m < cl := lt_of_lt_of_le (lt_of_lt_of_le h2 (min_le_right _ _)) (min_le_right _ _)
      rw [Finset.mem_filter]
      exact ⟨hmI, (mul_le_iff_lt m k N M H hmI).mpr (by rw [← hck]; exact hklt),
        (mul_le_iff_lt m l N M H hmI).mpr (by rw [← hcl]; exact hllt)⟩
  have hsum : ∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N ∧ m * l ≤ N then Ez (((k : ℝ) - (l : ℝ)) * (m : ℝ) * t) else 0)
      = ∑ m ∈ Finset.Ico M (min (M + H) (min ck cl)), Ez ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) := by
    rw [← Finset.sum_filter, hset]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    ring
  rw [hsum]
  refine geom_Ico_norm_le H _ ?_
  have hle : min (M + H) (min ck cl) ≤ M + H := min_le_left _ _
  rw [Nat.sub_le_iff_le_add]
  simpa [Nat.add_comm] using hle

lemma pair_sum_bound (N M H : ℕ) (b : ℕ → ℂ) (t : ℝ) (k l : ℕ) :
    ‖∑ m ∈ Finset.Ico M (M + H), wfun N b t k m * star (wfun N b t l m)‖
      ≤ ‖b k‖ * ‖b l‖ * capz H (((k : ℝ) - (l : ℝ)) * t) := by
  have hnorm : ‖b k * star (b l)‖ = ‖b k‖ * ‖b l‖ := by
    rw [norm_mul, norm_star]
  rw [pair_sum N M H b t k l, norm_mul, hnorm]
  exact mul_le_mul_of_nonneg_left (prefix_sum_bound N M H k l t) (by positivity)

lemma energy_bound (N M H : ℕ) (K : Finset ℕ) (b : ℕ → ℂ) (t : ℝ) :
    ∑ m ∈ Finset.Ico M (M + H), ‖∑ k ∈ K, wfun N b t k m‖ ^ 2
      ≤ ∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ * capz H (((k : ℝ) - (l : ℝ)) * t) := by
  classical
  have hsq : ∀ m, ‖∑ k ∈ K, wfun N b t k m‖ ^ 2
      = ((∑ k ∈ K, wfun N b t k m) * star (∑ k ∈ K, wfun N b t k m)).re := by
    intro m
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  have hexp : ∀ m, (∑ k ∈ K, wfun N b t k m) * star (∑ k ∈ K, wfun N b t k m)
      = ∑ k ∈ K, ∑ l ∈ K, wfun N b t k m * star (wfun N b t l m) := by
    intro m
    rw [star_sum, Finset.sum_mul_sum]
  have htot : ∑ m ∈ Finset.Ico M (M + H), ‖∑ k ∈ K, wfun N b t k m‖ ^ 2
      = (∑ k ∈ K, ∑ l ∈ K, ∑ m ∈ Finset.Ico M (M + H),
          wfun N b t k m * star (wfun N b t l m)).re := by
    rw [Finset.sum_congr rfl (fun m _ => hsq m), ← Complex.re_sum]
    congr 1
    rw [Finset.sum_congr rfl (fun m _ => hexp m), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
  rw [htot]
  refine le_trans (Complex.re_le_norm _) ?_
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k _ => ?_))
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l _ => ?_))
  exact pair_sum_bound N M H b t k l

lemma cauchy_step (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    ‖∑ m ∈ Finset.Ico M (M + H), a m * ∑ k ∈ K, wfun N b t k m‖ ^ 2
      ≤ (∑ m ∈ Finset.Ico M (M + H), ‖a m‖ ^ 2) *
          (∑ m ∈ Finset.Ico M (M + H), ‖∑ k ∈ K, wfun N b t k m‖ ^ 2) := by
  have h1 : ‖∑ m ∈ Finset.Ico M (M + H), a m * ∑ k ∈ K, wfun N b t k m‖
      ≤ ∑ m ∈ Finset.Ico M (M + H), ‖a m‖ * ‖∑ k ∈ K, wfun N b t k m‖ := by
    calc ‖∑ m ∈ Finset.Ico M (M + H), a m * ∑ k ∈ K, wfun N b t k m‖
        ≤ ∑ m ∈ Finset.Ico M (M + H), ‖a m * ∑ k ∈ K, wfun N b t k m‖ := norm_sum_le _ _
      _ = ∑ m ∈ Finset.Ico M (M + H), ‖a m‖ * ‖∑ k ∈ K, wfun N b t k m‖ := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [norm_mul]
  have h2 : (∑ m ∈ Finset.Ico M (M + H), ‖a m‖ * ‖∑ k ∈ K, wfun N b t k m‖) ^ 2
      ≤ (∑ m ∈ Finset.Ico M (M + H), ‖a m‖ ^ 2) *
          (∑ m ∈ Finset.Ico M (M + H), ‖∑ k ∈ K, wfun N b t k m‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2

lemma main_gen (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    ‖∑ m ∈ Finset.Ico M (M + H), a m * ∑ k ∈ K, wfun N b t k m‖ ^ 2
      ≤ (∑ m ∈ Finset.Ico M (M + H), ‖a m‖ ^ 2) *
          (∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ * capz H (((k : ℝ) - (l : ℝ)) * t)) := by
  refine le_trans (cauchy_step N M H K a b t) ?_
  refine mul_le_mul_of_nonneg_left (energy_bound N M H K b t) ?_
  exact Finset.sum_nonneg (fun m _ => by positivity)

end TSB

theorem Conjectures.Goldbach.TypeIiSpacingBound :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let cap (H : ℕ) (x : ℝ) := if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖);
    ∀ (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ), let I := Finset.Ico M (M+H);
      ‖∑ m ∈ I, a m * ∑ k ∈ K, (if m*k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)‖ ^ 2 ≤
        (∑ m ∈ I, ‖a m‖ ^ 2) *
          (∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - (l : ℝ)) * t)) := by
  dsimp only
  intro N M H K a b t
  exact TSB.main_gen N M H K a b t
