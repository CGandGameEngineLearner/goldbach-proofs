import Mathlib

-- child 1 zh: 在原题的中心候选集合中，对任意 ε > 0，充分大偶数 N 的非平方自由补数个数至多为 ε 乘以候选总数。
-- child 1 en: For every ε > 0 and all sufficiently large even N, at most ε times the size of the central candidate set have a complement divisible by a prime square.
-- child 2 zh: 存在固定 δ > 0，使充分大偶数 N 的中心候选中，补数平方自由且有三个素因子的个数至多为候选总数的 (3/10 − δ) 倍。
-- child 2 en: For some fixed δ > 0 and all sufficiently large even N, candidates whose complement is a product of three distinct primes number at most (3/10 − δ) times the size of the central candidate set.

theorem Conjectures.Cuts.Cut0d06a140b160c7f202179ef7
    (hsquares :
      let C := fun N : ℕ => (Finset.range N).filter (fun p =>
        Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5)
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
        (((C N).filter (fun p => ¬ Squarefree (N-p))).card : ℝ) ≤ ε * ((C N).card : ℝ))
    (htriples :
      let C := fun N : ℕ => (Finset.range N).filter (fun p =>
        Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5)
      ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
        (((C N).filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3 ∧
          Squarefree (N-p))).card : ℝ) ≤ (3/10 - δ) * ((C N).card : ℝ)) :
    (let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5); ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → 10*((C N).filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3)).card ≤ 3*(C N).card) := by
  classical
  intro C
  obtain ⟨δ, hδ, N₁, h₁⟩ := htriples
  obtain ⟨N₂, h₂⟩ := hsquares δ hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN heven
  let A := C N
  let T := A.filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3)
  let Q := fun p : ℕ => Squarefree (N-p)
  have hgood : ((T.filter Q).card : ℝ) ≤ (3/10 - δ) * (A.card : ℝ) := by
    have h := h₁ N ((le_max_left _ _).trans hN) heven
    simpa only [T, A, C, Q, Finset.filter_filter] using h
  have hbad : ((A.filter (fun p => ¬ Q p)).card : ℝ) ≤ δ * (A.card : ℝ) :=
    h₂ N ((le_max_right _ _).trans hN) heven
  have hsub : T.filter (fun p => ¬ Q p) ⊆ A.filter (fun p => ¬ Q p) := by
    intro p hp
    obtain ⟨ht, hq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, hq⟩
  have hsmall : ((T.filter (fun p => ¬ Q p)).card : ℝ) ≤ δ * (A.card : ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hbad
  have hsplit : (((T.filter Q).card : ℝ) + ((T.filter (fun p => ¬ Q p)).card : ℝ)) =
      (T.card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := T) Q
  have htotal : 10 * (T.card : ℝ) ≤ 3 * (A.card : ℝ) := by
    linarith [show (3/10 - δ) * (A.card : ℝ) + δ * (A.card : ℝ) =
      (3/10) * (A.card : ℝ) by ring]
  exact_mod_cast htotal
