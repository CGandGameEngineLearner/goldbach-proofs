import Mathlib


namespace GoldbachThinNumeric

/-- The union of the failure sets of at most `M` targets cannot fill the
sample space when each target has at least `8^k` admissible witnesses. -/
theorem budget_avoids (k M N : ℕ) (hM : M ≤ 16^(k+1)) (hD : 8^k ≤ N)
    (hN : N ≤ 16^(k+1)) :
    M*(N-8^k)^(80*4^k) < N^(80*4^k) := by
  let s : ℕ := 80*4^k
  have hNpos : 0 < N := (pow_pos (by decide : 0 < (8:ℕ)) _).trans_le hD
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hNpos
  have hdensity :
      (((N-8^k:ℕ):ℝ)/(N:ℝ)) ≤ Real.exp (-((8:ℝ)^k/(N:ℝ))) := by
    rw [Nat.cast_sub hD, Nat.cast_pow, Nat.cast_ofNat, sub_div, div_self hNR.ne']
    linarith only [Real.add_one_le_exp (-((8:ℝ)^k/(N:ℝ)))]
  have hNbound : (N:ℝ) ≤ (16:ℝ)^(k+1) := by exact_mod_cast hN
  have hscale : 5*(2:ℝ)^k ≤ (s:ℝ)*((8:ℝ)^k/(N:ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hNR).mpr
    calc
      _ ≤ (5*(2:ℝ)^k)*(16:ℝ)^(k+1) :=
        mul_le_mul_of_nonneg_left hNbound (by positivity)
      _ = 80*((2:ℝ)^k*(16:ℝ)^k) := by rw [pow_succ (16:ℝ)]; ring
      _ = 80*((4:ℝ)^k*(8:ℝ)^k) := by
        rw [← mul_pow, ← mul_pow]
        norm_num
      _ = _ := by
        dsimp only [s]
        push_cast
        ring
  have hs : (((N-8^k:ℕ):ℝ)/(N:ℝ))^s ≤ Real.exp (-(5*(2:ℝ)^k)) := calc
    _ ≤ (Real.exp (-((8:ℝ)^k/(N:ℝ))))^s :=
      pow_le_pow_left₀ (by positivity) hdensity s
    _ = Real.exp (-((s:ℝ)*((8:ℝ)^k/(N:ℝ)))) := by
      rw [← Real.exp_nat_mul, mul_neg]
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg hscale)
  have hlevel (j : ℕ) : j+1 ≤ (2:ℕ)^j := by
    induction j with
    | zero => decide
    | succ k ih =>
      rw [pow_succ]
      omega
  have hlevelR : (k:ℝ)+1 ≤ (2:ℝ)^k := by exact_mod_cast hlevel k
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
  have hlog : Real.log ((16:ℝ)^(k+1)) ≤ 4*(2:ℝ)^k := calc
    _ = ((k:ℝ)+1)*(4*Real.log 2) := by
      rw [Real.log_pow, show (16:ℝ)=(2:ℝ)^4 by norm_num, Real.log_pow]
      push_cast
      ring
    _ ≤ ((k:ℝ)+1)*(4:ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlog2]) (by positivity)
    _ ≤ _ := by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hlevelR (show (0:ℝ) ≤ 4 by norm_num)
  have hMexp : (M:ℝ) ≤ Real.exp (4*(2:ℝ)^k) := calc
    _ ≤ (16:ℝ)^(k+1) := by exact_mod_cast hM
    _ = Real.exp (Real.log ((16:ℝ)^(k+1))) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog
  have hsmall : (M:ℝ)*((((N-8^k:ℕ):ℝ)/(N:ℝ))^s) < 1 := calc
    _ ≤ Real.exp (4*(2:ℝ)^k)*Real.exp (-(5*(2:ℝ)^k)) :=
      mul_le_mul hMexp hs (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (-((2:ℝ)^k)) := by rw [← Real.exp_add]; congr 1; ring
    _ < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  rw [div_pow, ← mul_div_assoc] at hsmall
  exact_mod_cast (div_lt_one (pow_pos hNR s)).mp hsmall

end GoldbachThinNumeric


namespace GoldbachThinFiniteCover

open Finset

/-- There are fewer sequences missing a target than there are sequences of available points. -/
theorem finite_cover
    (numerical : ∀ k M N : ℕ, M ≤ 16 ^ (k + 1) → 8 ^ k ≤ N →
      N ≤ 16 ^ (k + 1) →
      M * (N - 8 ^ k) ^ (80 * 4 ^ k) < N ^ (80 * 4 ^ k))
    (k : ℕ) (T P : Finset ℕ) (edge : ℕ → ℕ → Bool)
    (hT : T.card ≤ 16 ^ (k + 1)) (hP : P.card ≤ 16 ^ (k + 1))
    (hCoverage : ∀ t ∈ T, 8 ^ k ≤ (P.filter fun p => edge t p = true).card) :
    ∃ B ⊆ P, B.card ≤ 80 * 4 ^ k ∧ ∀ t ∈ T, ∃ p ∈ B, edge t p = true := by
  classical
  by_cases hNonempty : T.Nonempty
  · obtain ⟨t₀, ht₀⟩ := hNonempty
    have hPmin : 8 ^ k ≤ P.card := (hCoverage t₀ ht₀).trans (card_filter_le _ _)
    let length := 80 * 4 ^ k
    let sequences := Fintype.piFinset (fun _ : Fin length => P)
    let avoiding (t : ℕ) := P.filter fun p => ¬ edge t p = true
    let missed (t : ℕ) := Fintype.piFinset (fun _ : Fin length => avoiding t)
    have hMissed (t : ℕ) (ht : t ∈ T) :
        (missed t).card ≤ (P.card - 8 ^ k) ^ length := by
      change (Fintype.piFinset fun _ : Fin length => avoiding t).card ≤ _
      rw [Fintype.card_piFinset_const]
      apply Nat.pow_le_pow_left
      have hPartition := card_filter_add_card_filter_not (s := P) (fun p => edge t p = true)
      have hLower := hCoverage t ht
      dsimp [avoiding]
      omega
    have hSmaller : (T.biUnion missed).card < sequences.card := by
      calc
        (T.biUnion missed).card ≤ T.card * (P.card - 8 ^ k) ^ length :=
          card_biUnion_le_card_mul T missed _ hMissed
        _ < P.card ^ length := numerical k T.card P.card hT hPmin hP
        _ = sequences.card := (Fintype.card_piFinset_const P length).symm
    obtain ⟨f, hf, hNotMissed⟩ := exists_mem_notMem_of_card_lt_card hSmaller
    refine ⟨univ.image f, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨i, _, rfl⟩ := mem_image.mp hp
      exact Fintype.mem_piFinset.mp hf i
    · exact card_image_le.trans (by simp [length])
    · intro t ht
      by_contra hNoHit
      have hAvoids : f ∈ missed t := by
        apply Fintype.mem_piFinset.mpr
        intro i
        refine mem_filter.mpr ⟨Fintype.mem_piFinset.mp hf i, ?_⟩
        intro hEdge
        exact hNoHit ⟨f i, mem_image.mpr ⟨i, mem_univ i, rfl⟩, hEdge⟩
      exact hNotMissed (mem_biUnion.mpr ⟨t, ht, hAvoids⟩)
  · refine ⟨∅, empty_subset _, by simp, ?_⟩
    intro t ht
    exact (hNonempty ⟨t, ht⟩).elim

end GoldbachThinFiniteCover


theorem Conjectures.Cuts.Task744db76e3724fd41c764bde6 :
    ∀ (x1 : ℕ) (x2 x3 : Finset ℕ) (x4 : ℕ → ℕ → Bool), x2.card ≤ (16 : ℕ) ^ (x1 + (1 : ℕ)) → x3.card ≤ (16 : ℕ) ^ (x1 + (1 : ℕ)) → (∀ x7 ∈ x2, (8 : ℕ) ^ x1 ≤ {x9 ∈ x3 | x4 x7 x9 = Bool.true}.card) → ∃ x8 ⊆ x3, x8.card ≤ (80 : ℕ) * (4 : ℕ) ^ x1 ∧ ∀ x9 ∈ x2, ∃ x11 ∈ x8, x4 x9 x11 = Bool.true :=
  GoldbachThinFiniteCover.finite_cover GoldbachThinNumeric.budget_avoids
