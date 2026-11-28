import Mathlib

-- child 1 zh: 构造支撑大小平方至多为 N/2 的均值一非负权，使四次矩一致有界且 Fourier 偏差任意小。
-- child 1 en: Construct mean-one nonnegative weights with bounded fourth moment and small Fourier error, supported on a set whose squared size is at most N/2.
-- child 2 zh: 在任意非零有限剩余群上，若实函数支撑在 A 上且 2|A|² ≤ N，则自卷积至少在一半元素上为零。
-- child 2 en: On a cyclic group of nonzero order N, a real function supported on A with twice the squared cardinality of A at most N has zero self-convolution at at least half the targets.

theorem Conjectures.Cuts.Cut1098874d8cd10c71cb980f3a
  (h₁ : (by
  classical
  exact ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, ∃ k : ℕ, Nat.Prime (k+1) ∧ T ≤ k+1 ∧ ∃ f : ZMod (k+1 : ℕ) → ℝ,
    let ft := fun (h : ZMod (k+1 : ℕ) → ℝ) (r : ZMod (k+1 : ℕ)) => (∑ x : ZMod (k+1 : ℕ), (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/((k+1 : ℕ) : ℂ)))/((k+1 : ℕ) : ℂ)
    (∀ x, 0 ≤ f x) ∧ (∑ x, f x)/((k+1 : ℕ):ℝ)=1 ∧ (∑ r : ZMod (k+1 : ℕ), ‖ft f r‖^4) ≤ M ∧ (∀ r, ‖ft (fun x => f x-1) r‖ ≤ ε) ∧ ∃ A : Finset (ZMod (k+1 : ℕ)), 2*A.card^2 ≤ (k+1 : ℕ) ∧ ∀ x, x ∉ A → f x = 0))
  (h₂ : (by
    classical
    exact ∀ (k : ℕ) (A : Finset (ZMod (k+1))) (f : ZMod (k+1) → ℝ),
      2*A.card^2 ≤ k+1 → (∀ x, x ∉ A → f x = 0) →
      ∃ Z : Finset (ZMod (k+1)), ((k+1 : ℕ) : ℝ)/2 ≤ (Z.card : ℝ) ∧
        ∀ n ∈ Z, (∑ x, f x * f (n-x)) = 0)) :
    (by
  classical
  exact ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, ∃ N : ℕ, ∃ hN : Nat.Prime N, T ≤ N ∧ (letI : NeZero N := ⟨hN.ne_zero⟩; ∃ f : ZMod N → ℝ,
    let ft := fun (h : ZMod N → ℝ) (r : ZMod N) => (∑ x : ZMod N, (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)
    (∀ x, 0 ≤ f x) ∧ (∑ x, f x)/(N:ℝ)=1 ∧ (∑ r : ZMod N, ‖ft f r‖^4) ≤ M ∧ (∀ r, ‖ft (fun x => f x-1) r‖ ≤ ε) ∧ (N:ℝ)/2 ≤ ((Finset.univ.filter (fun n : ZMod N => (∑ x, f x*f (n-x))=0)).card:ℝ))) := by
  classical
  obtain ⟨M, hM, hw⟩ := h₁
  refine ⟨M, hM, ?_⟩
  intro ε hε T
  obtain ⟨k, hp, hT, f, hpos, hmean, hfour, hunif, A, hsize, hsupp⟩ := hw ε hε T
  obtain ⟨Z, hZ, hzero⟩ := h₂ k A f hsize hsupp
  refine ⟨k+1, hp, hT, f, hpos, hmean, hfour, hunif, hZ.trans ?_⟩
  exact_mod_cast Finset.card_le_card (show Z ⊆
      Finset.univ.filter (fun n : ZMod (k+1) => (∑ x, f x * f (n-x)) = 0) from
    fun n hn => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero n hn⟩)
