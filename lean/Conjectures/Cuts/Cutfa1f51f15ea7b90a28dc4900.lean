import Mathlib

-- child 1 zh: 将固定宽度回文数字盒双射参数化为半长字母表元组，以镜像位权折叠计数目标交集并给出回文盒的精确幂次大小。
-- child 1 en: Parametrize the palindromic digit box by half-length digit tuples using folded mirror weights, counting target hits and the exact box cardinality.
-- child 2 zh: 利用单位圆加性特征正交性，将任意有限位权元组和命中目标集的计数表示为因子化三角多项式内积的实部。
-- child 2 en: Express the target-hit count of weighted digit-tuple sums as the real part of a factored trigonometric polynomial inner product on the unit interval.
-- child 3 zh: 对镜像位权 b^j + b^(k-1-j) 的因子化特征积与哥德巴赫偶数例外集的 Fourier 配对证明相对于回文盒规模的一致幂节省。
-- child 3 en: Bound the Fourier pairing of the folded mirror-weight product against even Goldbach exceptions with a uniform power saving in the palindromic box size.

theorem Conjectures.Cuts.Cutfa1f51f15ea7b90a28dc4900
    (h₁ : by
  classical
  exact ∀ b : ℕ, 2 ≤ b → ∀ D : Finset ℕ, D ⊆ Finset.range b → ∀ k : ℕ, ∀ R : Finset ℕ,
    let S := (Finset.range (b ^ k)).filter (fun n : ℕ => ∀ i < k, (n / b ^ i) % b ∈ D ∧ (n / b ^ i) % b = (n / b ^ (k - 1 - i)) % b)
    let m := (k + 1) / 2
    let w := fun j : Fin m => if 2 * j.1 + 1 = k then b ^ j.1 else b ^ j.1 + b ^ (k - 1 - j.1)
    let B := Fintype.piFinset (fun _ : Fin m => D)
    let v := fun c : Fin m → ℕ => ∑ j : Fin m, c j * w j
    (S.filter (fun n => n ∈ R)).card = (B.filter (fun c => v c ∈ R)).card ∧ S.card = D.card ^ m)
    (h₂ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))
  exact ∀ (m : ℕ) (D : Finset ℕ) (w : Fin m → ℕ) (R : Finset ℕ),
    let B := Fintype.piFinset (fun _ : Fin m => D)
    let v := fun c : Fin m → ℕ => ∑ j : Fin m, c j * w j
    (((B.filter (fun c => v c ∈ R)).card) : ℝ) =
      (∫ t in (0 : ℝ)..1, (∏ j : Fin m, ∑ d ∈ D, e (d * w j) t) * star (∑ n ∈ R, e n t)).re)
    (h₃ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))
  exact ∀ b : ℕ, 2 ≤ b → ∀ D : Finset ℕ, D ⊆ Finset.range b → 2 ≤ D.card →
    ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∀ k : ℕ,
      let m := (k + 1) / 2
      let w := fun j : Fin m => if 2 * j.1 + 1 = k then b ^ j.1 else b ^ j.1 + b ^ (k - 1 - j.1)
      ∀ R : Finset ℕ, R ⊆ Finset.range (b ^ k) →
        (∀ n ∈ R, Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n)) →
        ‖∫ t in (0 : ℝ)..1, (∏ j : Fin m, ∑ d ∈ D, e (d * w j) t) * star (∑ n ∈ R, e n t)‖ ≤
          C * (1 + ((D.card ^ m : ℕ) : ℝ)) ^ (1 - δ))
    : (by
  classical
  exact ∀ b : ℕ, 2≤b → ∀ D : Finset ℕ, D ⊆ Finset.range b → 2≤D.card → ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∀ k : ℕ, let S := (Finset.range (b^k)).filter (fun n : ℕ => ∀ i < k, (n/b^(i)) % b ∈ D ∧ (n/b^(i)) % b=(n/b^(k-1-i)) % b); (((S).filter (fun n : ℕ => Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n))).card:ℝ) ≤ C*(1+(S.card:ℝ))^(1-δ)) := by
  classical
  intro b hb D hD hDcard
  obtain ⟨δ, C, hδ0, hδ1, hC, hbound⟩ := h₃ b hb D hD hDcard
  refine ⟨δ, C, hδ0, hδ1, hC, ?_⟩
  intro k S
  let R := S.filter (fun n : ℕ => Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n))
  have hSR : S.filter (fun n => n ∈ R) = R := by
    ext n
    exact Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
  have hRrange : R ⊆ Finset.range (b ^ k) := by
    intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  have hRbad : ∀ n ∈ R, Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  obtain ⟨hcount, hsize⟩ := h₁ b hb D hD k R
  change (S.filter (fun n => n ∈ R)).card = _ at hcount
  rw [hSR] at hcount
  let m := (k + 1) / 2
  let w := fun j : Fin m => if 2 * j.1 + 1 = k then b ^ j.1 else b ^ j.1 + b ^ (k - 1 - j.1)
  change (R.card : ℝ) ≤ C * (1 + (S.card : ℝ)) ^ (1 - δ)
  rw [hcount, hsize, h₂ m D w R]
  exact (Complex.re_le_norm _).trans (hbound k R hRrange hRbad)
