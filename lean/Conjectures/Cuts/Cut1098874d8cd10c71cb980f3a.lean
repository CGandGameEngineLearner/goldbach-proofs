import Mathlib

-- child 1 zh: 构造支撑大小平方至多为 N/2 的均值一非负权，使四次矩一致有界且 Fourier 偏差任意小。
-- child 1 en: Construct mean-one nonnegative weights with bounded fourth moment and small Fourier error, supported on a set whose squared size is at most N/2.
-- child 2 zh: 在任意非零有限剩余群上，若实函数支撑在 A 上且 2|A|² ≤ N，则自卷积至少在一半元素上为零。
-- child 2 en: On a cyclic group of nonzero order N, a real function supported on A with twice the squared cardinality of A at most N has zero self-convolution at at least half the targets.

theorem Conjectures.Cuts.Cut1098874d8cd10c71cb980f3a
  (h₁ : (by
  classical
  exact ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, ∃ N : ℕ, ∃ hN : Nat.Prime N, T ≤ N ∧ (letI : NeZero N := ⟨hN.ne_zero⟩; ∃ f : ZMod N → ℝ,
    let ft := fun (h : ZMod N → ℝ) (r : ZMod N) => (∑ x : ZMod N, (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)
    (∀ x, 0 ≤ f x) ∧ (∑ x, f x)/(N:ℝ)=1 ∧ (∑ r : ZMod N, ‖ft f r‖^4) ≤ M ∧ (∀ r, ‖ft (fun x => f x-1) r‖ ≤ ε) ∧ ∃ A : Finset (ZMod N), 2*A.card^2 ≤ N ∧ ∀ x, x ∉ A → f x = 0)))
  (h₂ : (by
    classical
    exact ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (f : ZMod N → ℝ),
      2*A.card^2 ≤ N → (∀ x, x ∉ A → f x = 0) →
      (N:ℝ)/2 ≤ ((Finset.univ.filter (fun n : ZMod N => (∑ x, f x*f (n-x))=0)).card:ℝ))) :
    (by
  classical
  exact ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, ∃ N : ℕ, ∃ hN : Nat.Prime N, T ≤ N ∧ (letI : NeZero N := ⟨hN.ne_zero⟩; ∃ f : ZMod N → ℝ,
    let ft := fun (h : ZMod N → ℝ) (r : ZMod N) => (∑ x : ZMod N, (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)
    (∀ x, 0 ≤ f x) ∧ (∑ x, f x)/(N:ℝ)=1 ∧ (∑ r : ZMod N, ‖ft f r‖^4) ≤ M ∧ (∀ r, ‖ft (fun x => f x-1) r‖ ≤ ε) ∧ (N:ℝ)/2 ≤ ((Finset.univ.filter (fun n : ZMod N => (∑ x, f x*f (n-x))=0)).card:ℝ))) := by
  classical
  obtain ⟨M, hM, hw⟩ := h₁
  refine ⟨M, hM, ?_⟩
  intro ε hε T
  obtain ⟨N, hp, hT, hN⟩ := hw ε hε T
  letI : NeZero N := ⟨hp.ne_zero⟩
  obtain ⟨f, hpos, hmean, hfour, hunif, A, hsize, hsupp⟩ := hN
  exact ⟨N, hp, hT, f, hpos, hmean, hfour, hunif, h₂ N A f hsize hsupp⟩
