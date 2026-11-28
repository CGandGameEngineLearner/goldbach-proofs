import Mathlib

-- child 1 zh: 确定任意非负整数最低 k 位的进位制数字加权和，包含截断和前导零。
-- child 1 en: Reconstruct the low k digits of every natural number as its exact remainder modulo the kth power of the base.
-- child 2 zh: 证明任意有界数字词的进位制编码落在正确范围，逐位除法和取余能恢复原词。
-- child 2 en: Bound the positionally encoded word and recover every digit for arbitrary bounded digits and word length.
-- child 3 zh: 对逐位变化的字母表，证明数字 Fourier 乘积与任意有限目标集的配对积分精确计算命中的词数。
-- child 3 en: Identify the pairing of a varying-alphabet Fourier product with any finite target set as the exact count of matching words.
-- child 4 zh: 在所有逐位数字盒上，对实际偶数哥德巴赫例外集的 Fourier 配对给出内在幂节省。
-- child 4 en: Bound the Fourier pairing with even Goldbach exceptions by a fixed power saving in the size of each varying digit box.

theorem Conjectures.Cuts.Cut92b73a4f12b1f2b08568edbf
    (h₁ : ∀ (b k n : ℕ), 2 ≤ b → (∑ i : Fin k, ((n/b^(i:ℕ)) % b)*b^(i:ℕ)) = n % b^k)
    (h₂ : ∀ (b k : ℕ), 2 ≤ b → ∀ w : Fin k → ℕ, (∀ i, w i < b) →
    let n := ∑ i : Fin k, w i*b^(i:ℕ)
    n < b^k ∧ ∀ i : Fin k, (n/b^(i:ℕ)) % b = w i)
    (h₃ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ (b k : ℕ) (D : ℕ → Finset ℕ) (R : Finset ℕ),
    let W := Fintype.piFinset (fun i : Fin k => D i)
    let v := fun w : Fin k → ℕ => ∑ i : Fin k, w i*b^(i:ℕ)
    (((W.filter (fun w => v w ∈ R)).card):ℝ) = (∫ t in (0:ℝ)..1, (∏ i : Fin k, ∑ d ∈ D i, e (d*b^(i:ℕ)) t) * star (∑ n ∈ R, e n t)).re)
    (h₄ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ b : ℕ, 2 ≤ b → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∀ k : ℕ, ∀ D : ℕ → Finset ℕ,
    (∀ i < k, D i ⊆ Finset.range b ∧ 2 ≤ (D i).card) → ∀ R : Finset ℕ,
    (∀ n ∈ R, Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) →
    ‖∫ t in (0:ℝ)..1, (∏ i : Fin k, ∑ d ∈ D i, e (d*b^(i:ℕ)) t) * star (∑ n ∈ R, e n t)‖ ≤ C*(1+((∏ i : Fin k, (D i).card : ℕ):ℝ))^(1-δ))
    : (by
  classical
  exact ∀ b : ℕ, 2≤b → ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∀ k : ℕ, ∀ D : ℕ → Finset ℕ, (∀ i < k, D i ⊆ Finset.range b ∧ 2≤(D i).card) → let S := (Finset.range (b^k)).filter (fun n : ℕ => ∀ i < k, (n/b^(i)) % b ∈ D i); (((S).filter (fun n : ℕ => Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n))).card:ℝ) ≤ C*(1+(S.card:ℝ))^(1-δ)) := by
  classical
  intro b hb
  obtain ⟨δ,C,hδ,h₁δ,hC,h⟩ := h₄ b hb
  refine ⟨δ,C,hδ,h₁δ,hC,?_⟩
  intro k D hD S
  let W := Fintype.piFinset (fun i : Fin k => D i)
  let v := fun w : Fin k → ℕ => ∑ i : Fin k, w i*b^(i:ℕ)
  have digits (w : Fin k → ℕ) (hw : w ∈ W) :
      v w < b^k ∧ ∀ i : Fin k, (v w/b^(i:ℕ)) % b = w i :=
    h₂ b k hb w (fun i => Finset.mem_range.mp ((hD i i.isLt).1 ((Fintype.mem_piFinset.mp hw) i)))
  have inj : Set.InjOn v W := by
    intro u hu w hw he
    funext i
    exact ((digits u hu).2 i).symm.trans (he ▸ (digits w hw).2 i)
  have image : W.image v = S := by
    ext n
    constructor
    · intro hn
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (digits w hw).1, ?_⟩
      intro i hi
      have he := (digits w hw).2 ⟨i,hi⟩
      rw [show v w / b^i % b = w ⟨i,hi⟩ from he]
      exact Fintype.mem_piFinset.mp hw ⟨i,hi⟩
    · intro hn
      obtain ⟨hn,hd⟩ := Finset.mem_filter.mp hn
      let w := fun i : Fin k => (n/b^(i:ℕ)) % b
      refine Finset.mem_image.mpr ⟨w, Fintype.mem_piFinset.mpr (fun i => hd i i.isLt), ?_⟩
      exact (h₁ b k n hb).trans (Nat.mod_eq_of_lt (Finset.mem_range.mp hn))
  have size : S.card = ∏ i : Fin k, (D i).card := by
    rw [← image, Finset.card_image_of_injOn inj]
    exact Fintype.card_piFinset _
  let R := S.filter (fun n : ℕ => Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n)
  have sub : R ⊆ S := Finset.filter_subset _ _
  have him : (W.filter (fun w => v w ∈ R)).image v = R := by
    ext n
    constructor
    · intro hn
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hn
      exact (Finset.mem_filter.mp hw).2
    · intro hn
      have hs := sub hn
      rw [← image] at hs
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,hn⟩,rfl⟩
  have count : R.card = (W.filter (fun w => v w ∈ R)).card := by
    exact (congrArg Finset.card him.symm).trans (Finset.card_image_of_injOn (inj.mono (Finset.filter_subset _ _)))
  change (R.card : ℝ) ≤ C*(1+(S.card:ℝ))^(1-δ)
  rw [count,size,h₃ b k D R]
  exact le_trans (Complex.re_le_norm _) (h k D hD R (fun n hn => (Finset.mem_filter.mp hn).2))
