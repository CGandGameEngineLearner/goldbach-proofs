import Mathlib

namespace PPTAux

open Finset

/-- von Mangoldt restricted to non-primes. -/
noncomputable def a (m : ℕ) : ℝ := if ¬ m.Prime then ArithmeticFunction.vonMangoldt m else 0

noncomputable def g (m : ℕ) : ℝ := Real.log ((m : ℝ) + 2) / (m : ℝ)

noncomputable def H (m : ℕ) : ℝ := (Real.log ((m : ℝ) + 2) + 2) / Real.sqrt (m : ℝ)

lemma a_nonneg (m : ℕ) : 0 ≤ a m := by
  unfold a
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma log_nonneg' (m : ℕ) : 0 ≤ Real.log ((m : ℝ) + 2) :=
  Real.log_nonneg (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])

lemma g_nonneg (m : ℕ) : 0 ≤ g m :=
  div_nonneg (log_nonneg' m) (Nat.cast_nonneg m)

lemma H_nonneg (m : ℕ) : 0 ≤ H m :=
  div_nonneg (by linarith [log_nonneg' m]) (Real.sqrt_nonneg _)

lemma log_step (x : ℝ) (hx : 0 ≤ x) : Real.log (x + 3) ≤ Real.log (x + 2) + 1 / (x + 2) := by
  have h2 : 0 < x + 2 := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 3) / (x + 2) by positivity)
  rw [Real.log_div (by linarith) (by linarith)] at h
  have e : (x + 3) / (x + 2) - 1 = 1 / (x + 2) := by field_simp; ring
  linarith

lemma g_anti (n : ℕ) (hn : 1 ≤ n) : g (n + 1) ≤ g n := by
  unfold g
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  have e3 : (n : ℝ) + 1 + 2 = n + 3 := by ring
  rw [e3, div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 := log_step n (by linarith)
  have h2 : 1 - ((n : ℝ) + 2)⁻¹ ≤ Real.log ((n : ℝ) + 2) :=
    Real.one_sub_inv_le_log_of_pos (by linarith)
  have hu : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
  have hu1 : ((n : ℝ) + 2)⁻¹ * ((n : ℝ) + 2) = 1 := inv_mul_cancel₀ (by linarith)
  rw [one_div] at h1
  set u := ((n : ℝ) + 2)⁻¹
  set L2 := Real.log ((n : ℝ) + 2)
  set L3 := Real.log ((n : ℝ) + 3)
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show (0 : ℝ) ≤ n by linarith)]

lemma real_ineq (s t L l : ℝ) (hs : 0 < s) (hst : s < t) (h : t ^ 2 = s ^ 2 + 1) (hL : 0 ≤ L)
    (hl : L - 1 / t ^ 2 ≤ l) : (t - s) * (L / t ^ 2) ≤ (l + 2) / s - (L + 2) / t := by
  have ht : 0 < t := by linarith
  have h1 : (L - 1 / t ^ 2 + 2) / s ≤ (l + 2) / s :=
    div_le_div_of_nonneg_right (by linarith) hs.le
  have h2 : (t - s) * (L / t ^ 2) ≤ (L - 1 / t ^ 2 + 2) / s - (L + 2) / t := by
    rw [← sub_nonneg]
    have e : (L - 1 / t ^ 2 + 2) / s - (L + 2) / t - (t - s) * (L / t ^ 2)
        = ((t - s) * (L * (t - s) + 2 * t) - 1) / (s * t ^ 2) := by
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg hL (sq_nonneg (t - s)), sq_nonneg (t - s)]
  linarith

lemma sqrt_tel (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) * g (n + 1) ≤ H n - H (n + 1) := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
  have ht2 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 := by
    rw [Real.sq_sqrt (by positivity)]; push_cast; ring
  have hst : Real.sqrt (n : ℝ) < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_lt_sqrt (by linarith) (by push_cast; linarith)
  have e3 : (((n + 1 : ℕ) : ℝ)) + 2 = n + 3 := by push_cast; ring
  have hstep := log_step n (by linarith)
  have hle : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have key := real_ineq (Real.sqrt (n : ℝ)) (Real.sqrt ((n + 1 : ℕ) : ℝ)) (Real.log ((n : ℝ) + 3))
    (Real.log ((n : ℝ) + 2)) hs hst (by rw [ht2, hs2])
    (Real.log_nonneg (by linarith)) (by rw [ht2]; linarith)
  unfold g H
  rw [e3]
  rw [ht2] at key
  have e1 : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [show Real.log ((n : ℝ) + 3) / ((n + 1 : ℕ) : ℝ) = Real.log ((n : ℝ) + 3) / ((n : ℝ) + 1) by
    rw [e1]]
  exact key

lemma abel (b : ℕ) (w g H B : ℕ → ℝ)
    (hW : ∀ N, b ≤ N → ∑ m ∈ Icc b N, w m ≤ B N)
    (hg : ∀ n, b ≤ n → g (n + 1) ≤ g n)
    (hg0 : ∀ n, b ≤ n → 0 ≤ g n)
    (hH : ∀ n, b ≤ n → (B (n + 1) - B n) * g (n + 1) ≤ H n - H (n + 1))
    (hH0 : ∀ n, b ≤ n → 0 ≤ H n) (N : ℕ) (hN : b ≤ N) :
    ∑ m ∈ Icc b N, w m * g m ≤ B b * g b + H b := by
  have key : ∀ N, b ≤ N →
      ∑ m ∈ Icc b N, w m * g m + (B N - ∑ m ∈ Icc b N, w m) * g N + H N ≤ B b * g b + H b := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [Icc_self, sum_singleton]
      apply le_of_eq
      ring
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have h1 := hW N hN
      have h2 := hg N hN
      have h3 := hH N hN
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have h := key N hN
  nlinarith [mul_nonneg (sub_nonneg.mpr (hW N hN)) (hg0 N hN), hH0 N hN]

lemma sum_a_le : ∃ C : ℝ, 0 < C ∧ ∀ b N : ℕ, 1 ≤ b →
    ∑ m ∈ Icc b N, a m ≤ C * Real.sqrt (N : ℝ) := by
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro b N hb
  have h1 := Chebyshev.psi_sub_theta_eq_sum_not_prime (N : ℝ)
  rw [Nat.floor_natCast] at h1
  have h2 : ∑ m ∈ Icc b N, a m ≤ ∑ m ∈ Ioc 0 N, a m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      simp only [mem_Icc, mem_Ioc] at hm ⊢
      omega
    · intro m _ _
      exact a_nonneg m
  have h3 : ∑ m ∈ Ioc 0 N, a m
      = ∑ m ∈ Ioc 0 N with ¬ m.Prime, ArithmeticFunction.vonMangoldt m := by
    rw [Finset.sum_filter]
    rfl
  have h4 := hC₀ (N : ℝ)
  have h5 : C₀ * Real.sqrt (N : ℝ) ≤ max C₀ 1 * Real.sqrt (N : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  linarith

lemma sum_ag_le : ∃ C : ℝ, 0 < C ∧ ∀ b N : ℕ, 1 ≤ b →
    ∑ m ∈ Icc b N, a m * g m ≤ C * (Real.sqrt (b : ℝ) * g b + H b) := by
  obtain ⟨C, hC, hCb⟩ := sum_a_le
  refine ⟨C, hC, ?_⟩
  intro b N hb
  rcases lt_or_ge N b with hN | hN
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    exact mul_nonneg hC.le (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (g_nonneg b)) (H_nonneg b))
  · have := abel b a g (fun n => C * H n) (fun n => C * Real.sqrt (n : ℝ))
      (fun N _ => hCb b N hb)
      (fun n hn => g_anti n (le_trans hb hn))
      (fun n _ => g_nonneg n)
      (fun n hn => by
        have h := sqrt_tel n (le_trans hb hn)
        have := mul_le_mul_of_nonneg_left h hC.le
        linarith)
      (fun n _ => mul_nonneg hC.le (H_nonneg n)) N hN
    linarith

lemma term_le (n : ℕ) (h : ¬ n.Prime ∨ ¬ (n + 2).Prime) :
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) / ((n : ℝ) + 2)
      ≤ a n * g n + a (n + 2) * g (n + 2) := by
  have hΛ0 : ∀ m : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt m :=
    fun m => ArithmeticFunction.vonMangoldt_nonneg
  have hΛl : ∀ m : ℕ, ArithmeticFunction.vonMangoldt m ≤ Real.log m :=
    fun m => ArithmeticFunction.vonMangoldt_le_log
  have hnn : 0 ≤ a n * g n := mul_nonneg (a_nonneg _) (g_nonneg _)
  have hnn2 : 0 ≤ a (n + 2) * g (n + 2) := mul_nonneg (a_nonneg _) (g_nonneg _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show ArithmeticFunction.vonMangoldt 0 = 0 from by simp, zero_mul, zero_div]
    linarith
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases h with h | h
  · have ha : a n = ArithmeticFunction.vonMangoldt n := by simp [a, h]
    have h1 : ArithmeticFunction.vonMangoldt (n + 2) / ((n : ℝ) + 2) ≤ g n := by
      unfold g
      have := hΛl (n + 2)
      push_cast at this
      exact div_le_div₀ (log_nonneg' n) this (by linarith) (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 (hΛ0 n)
    rw [ha]
    rw [mul_div_assoc]
    linarith
  · have ha : a (n + 2) = ArithmeticFunction.vonMangoldt (n + 2) := by simp [a, h]
    have h1 : ArithmeticFunction.vonMangoldt n / ((n : ℝ) + 2) ≤ g (n + 2) := by
      unfold g
      push_cast
      have h0 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2 + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      exact div_le_div₀ (Real.log_nonneg (by linarith)) (le_trans (hΛl n) h0) (by linarith) le_rfl
    have h2 := mul_le_mul_of_nonneg_left h1 (hΛ0 (n + 2))
    rw [ha]
    have e : ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) / ((n : ℝ) + 2)
        = ArithmeticFunction.vonMangoldt (n + 2) * (ArithmeticFunction.vonMangoldt n / ((n : ℝ) + 2)) := by
      ring
    rw [e]
    linarith

lemma final_bound (b : ℕ) (hb : 1 ≤ b) :
    Real.sqrt (b : ℝ) * g b + H b
      ≤ 8 * Real.log (2 + ((b + 1 : ℕ) : ℝ)) / Real.sqrt ((b + 1 : ℕ) : ℝ) := by
  have hx : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hs : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (b : ℝ) * Real.sqrt (b : ℝ) = b := Real.mul_self_sqrt (by linarith)
  have hU : 0 < Real.sqrt ((b + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hUle : Real.sqrt ((b + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (b : ℝ) := by
    rw [show (2 : ℝ) * Real.sqrt (b : ℝ) = Real.sqrt (4 * (b : ℝ)) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    push_cast
    linarith
  have hlog : Real.log ((b : ℝ) + 2) ≤ Real.log (2 + ((b + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log (by linarith)
    push_cast
    linarith
  have hlog1 : 1 ≤ Real.log (2 + ((b + 1 : ℕ) : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    push_cast
    linarith
  have e : Real.sqrt (b : ℝ) * g b + H b
      = (2 * Real.log ((b : ℝ) + 2) + 2) / Real.sqrt (b : ℝ) := by
    unfold g H
    rw [eq_div_iff hs.ne']
    have hb0 : (b : ℝ) ≠ 0 := by linarith
    field_simp
    nlinarith [hs2]
  rw [e, div_le_div_iff₀ hs hU]
  set L := Real.log (2 + ((b + 1 : ℕ) : ℝ))
  set l := Real.log ((b : ℝ) + 2)
  set s := Real.sqrt (b : ℝ)
  set t := Real.sqrt ((b + 1 : ℕ) : ℝ)
  have hl0 : 0 ≤ l := log_nonneg' b
  nlinarith [mul_nonneg (show 0 ≤ 2 * l + 2 by linarith) (sub_nonneg.mpr hUle),
    mul_nonneg (show 0 ≤ 4 * L - (2 * l + 2) by linarith) hs.le]

end PPTAux

theorem Conjectures.TwinPrimes.HarmonicProperPowerTail : (∃ C : ℝ, 0<C ∧ ∀ U V : ℕ, 2≤U → (∑ n ∈ (Finset.range V).filter (fun n => U<n+2 ∧ (¬n.Prime ∨ ¬(n+2).Prime)), ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)/(n+2 : ℝ)) ≤ C*Real.log (2+U)/Real.sqrt U) := by
  obtain ⟨C, hC, hCb⟩ := PPTAux.sum_ag_le
  refine ⟨16 * C, by positivity, ?_⟩
  intro U V hU
  obtain ⟨b, rfl⟩ : ∃ b, U = b + 1 := ⟨U - 1, by omega⟩
  have hb : 1 ≤ b := by omega
  set S := (Finset.range V).filter (fun n => b + 1 < n + 2 ∧ (¬n.Prime ∨ ¬(n+2).Prime)) with hS
  have h1 : ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)/(n+2 : ℝ)
      ≤ ∑ n ∈ S, (PPTAux.a n * PPTAux.g n + PPTAux.a (n + 2) * PPTAux.g (n + 2)) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    exact PPTAux.term_le n hn.2.2
  rw [Finset.sum_add_distrib] at h1
  have h2 : ∑ n ∈ S, PPTAux.a n * PPTAux.g n ≤ ∑ m ∈ Finset.Icc b (V + 2), PPTAux.a m * PPTAux.g m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [hS, Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_Icc]
      omega
    · intro m _ _
      exact mul_nonneg (PPTAux.a_nonneg _) (PPTAux.g_nonneg _)
  have h3 : ∑ n ∈ S, PPTAux.a (n + 2) * PPTAux.g (n + 2)
      ≤ ∑ m ∈ Finset.Icc b (V + 2), PPTAux.a m * PPTAux.g m := by
    have e : ∑ n ∈ S, PPTAux.a (n + 2) * PPTAux.g (n + 2)
        = ∑ m ∈ S.image (fun n => n + 2), PPTAux.a m * PPTAux.g m := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      simpa using hxy
    rw [e]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨n, hn, rfl⟩ := hm
      rw [hS, Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_Icc]
      omega
    · intro m _ _
      exact mul_nonneg (PPTAux.a_nonneg _) (PPTAux.g_nonneg _)
  have h4 := hCb b (V + 2) hb
  have h5 := PPTAux.final_bound b hb
  have h6 := mul_le_mul_of_nonneg_left h5 hC.le
  have e : 16 * C * Real.log (2 + ((b + 1 : ℕ) : ℝ)) / Real.sqrt ((b + 1 : ℕ) : ℝ)
      = 2 * (C * (8 * Real.log (2 + ((b + 1 : ℕ) : ℝ)) / Real.sqrt ((b + 1 : ℕ) : ℝ))) := by
    ring
  rw [e]
  linarith
