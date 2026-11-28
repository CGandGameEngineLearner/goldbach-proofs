import Mathlib

-- child 1 zh: 对任意有限目标集，证明固定重量零一数字层的交数等于 j 元位置集的命中数，并给出层的精确二项式大小。
-- child 1 en: Count hits of any finite target set on a binary digit layer by its j-element position sets and compute its exact binomial size.
-- child 2 zh: 对任意复数位权，通过单位圆 Fourier 积分提取多重仿射乘积中固定次数的全部子集权。
-- child 2 en: Extract an elementary symmetric sum of arbitrary complex position weights as a Fourier coefficient of their multiaffine product.
-- child 3 zh: 用加性特征正交性，计算固定大小位置子集的幂和命中给定整数集合的准确数目。
-- child 3 en: Count fixed-size subset sums that hit a finite target by pairing their phase products with the target characters.
-- child 4 zh: 在中央重量层上，对实际哥德巴赫例外集与双频数字乘积的配对给出一致幂节省。
-- child 4 en: Obtain a uniform power saving for the two-frequency digit product paired against actual Goldbach exceptions on central weight layers.

theorem Conjectures.Cuts.Cut031217652ef81e752af5ab9f
    (h₁ : by
  classical
  exact ∀ b k j : ℕ, 2 ≤ b → ∀ R : Finset ℕ,
    let S := (Finset.range (b^k)).filter (fun n : ℕ => (∀ i < k, (n/b^i) % b ≤ 1) ∧ ((Finset.range k).filter (fun i => (n/b^i) % b=1)).card=j)
    let B := (Finset.range k).powersetCard j
    let v := fun s : Finset ℕ => ∑ i ∈ s, b^i
    (S.filter (fun n => n ∈ R)).card = (B.filter (fun s => v s ∈ R)).card ∧ S.card = k.choose j)
    (h₂ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ (A : Finset ℕ) (c : ℕ → ℂ) (j : ℕ),
    (∫ u in (0:ℝ)..1, (∏ i ∈ A, (1+c i * e 1 u)) * star (e j u)) = ∑ s ∈ A.powersetCard j, ∏ i ∈ s, c i)
    (h₃ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ (A : Finset ℕ) (b j : ℕ) (R : Finset ℕ),
    let B := A.powersetCard j
    let v := fun s : Finset ℕ => ∑ i ∈ s, b^i
    (((B.filter (fun s => v s ∈ R)).card):ℝ) = (∫ t in (0:ℝ)..1, (∑ s ∈ B, ∏ i ∈ s, e (b^i) t) * star (∑ n ∈ R, e n t)).re)
    (h₄ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ b : ℕ, 2 ≤ b → ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∀ k j : ℕ, k≤4*j → 4*j≤3*k →
    ∀ R : Finset ℕ, (∀ n ∈ R, Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) →
    ‖∫ t in (0:ℝ)..1, (∫ u in (0:ℝ)..1, (∏ i ∈ Finset.range k, (1+e (b^i) t * e 1 u)) * star (e j u)) * star (∑ n ∈ R, e n t)‖ ≤ C*(1+(k.choose j:ℝ))^(1-δ))
    : (by
  classical
  exact ∀ b : ℕ, 2≤b → ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∀ k j : ℕ, k≤4*j → 4*j≤3*k → let S := (Finset.range (b^k)).filter (fun n : ℕ => (∀ i < k, (n/b^(i)) % b ≤ 1) ∧ ((Finset.range k).filter (fun i => (n/b^(i)) % b=1)).card=j); (((S).filter (fun n : ℕ => Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n))).card:ℝ) ≤ C*(1+(S.card:ℝ))^(1-δ)) := by
  classical
  intro b hb
  obtain ⟨δ,C,hδ,hδ₁,hC,h⟩ := h₄ b hb
  refine ⟨δ,C,hδ,hδ₁,hC,?_⟩
  intro k j hj hj' S
  let R := S.filter (fun n : ℕ => Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n)
  have he : S.filter (fun n => n ∈ R) = R := by
    ext n
    exact Finset.mem_filter.trans ⟨fun x => x.2, fun x => ⟨(Finset.mem_filter.mp x).1,x⟩⟩
  obtain ⟨count,size⟩ := h₁ b k j hb R
  change (S.filter (fun n => n ∈ R)).card = _ at count
  rw [he] at count
  change (R.card:ℝ) ≤ C*(1+(S.card:ℝ))^(1-δ)
  rw [count,size,h₃ (Finset.range k) b j R]
  have bound := h k j hj hj' R (fun n hn => (Finset.mem_filter.mp hn).2)
  simp_rw [h₂ (Finset.range k) _ j] at bound
  exact (Complex.re_le_norm _).trans bound
