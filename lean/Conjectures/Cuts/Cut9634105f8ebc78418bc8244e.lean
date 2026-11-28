import Mathlib

/-- Decomposition of L-goldbach-digital-central-representations.
child 1 zh: 任意自然数的低 k 位数字加权和等于它模 b^k 的余数。
child 1 en: The low k base-b digits of any natural number recombine to its remainder modulo b^k.
child 2 zh: 任意有界数字词的进位制编码落在 b^k 内，且逐位除法和取余恢复原词。
child 2 en: A bounded base-b word encodes below b^k and every digit is recovered by division and remainder.
child 3 zh: 数字 Fourier 乘积与任意有限目标集的配对积分等于命中的词数。
child 3 en: The pairing of the digit Fourier product with any finite target set is the exact count of matching words.
child 4 zh: 对实际偶数中心化哥德巴赫例外集的 Fourier 配对给出内在幂节省（解析输入）。
child 4 en: Analytic input: the Fourier pairing with even targets failing every centre-localized representation is power-saving in the digit box size.
-/

theorem Conjectures.Cuts.Cut9634105f8ebc78418bc8244e
    (h₁ : ∀ (b k n : ℕ), 2 ≤ b → (∑ i : Fin k, ((n/b^(i:ℕ)) % b)*b^(i:ℕ)) = n % b^k)
    (h₂ : ∀ (b k : ℕ), 2 ≤ b → ∀ w : Fin k → ℕ, (∀ i, w i < b) →
    let n := ∑ i : Fin k, w i*b^(i:ℕ)
    n < b^k ∧ ∀ i : Fin k, (n/b^(i:ℕ)) % b = w i)
    (h₃ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ (b k : ℕ) (D : Finset ℕ) (R : Finset ℕ),
    let W := Fintype.piFinset (fun _ : Fin k => D)
    let v := fun w : Fin k → ℕ => ∑ i : Fin k, w i*b^(i:ℕ)
    (((W.filter (fun w => v w ∈ R)).card):ℝ) = (∫ t in (0:ℝ)..1, (∏ i : Fin k, ∑ d ∈ D, e (d*b^(i:ℕ)) t) * star (∑ n ∈ R, e n t)).re)
    (h₄ : by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ b : ℕ, 2 ≤ b → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∀ k : ℕ, ∀ D : Finset ℕ,
    D ⊆ Finset.range b → 2 ≤ D.card → ∀ R : Finset ℕ,
    (∀ n ∈ R, Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ (Nat.dist p q)^3 ≤ n^2) →
    ‖∫ t in (0:ℝ)..1, (∏ i : Fin k, ∑ d ∈ D, e (d*b^(i:ℕ)) t) * star (∑ n ∈ R, e n t)‖ ≤ C*(1+(↑(∏ i : Fin k, D.card) : ℝ))^(1-δ))
    :
(by
  classical
  exact ∀ b : ℕ, 2≤b → ∀ D : Finset ℕ, D ⊆ Finset.range b → 2≤D.card → ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∀ k : ℕ, let S := (Finset.range (b^k)).filter (fun n : ℕ => ∀ i < k, (n/b^(i))%b ∈ D); (((S).filter (fun n : ℕ => Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ (Nat.dist p q)^3≤n^2)).card:ℝ) ≤ C*(1+(S.card:ℝ))^(1-δ)) := by
  classical
  intro b hb D hDsub hDcard
  obtain ⟨δ, C, hδ, hδ1, hC, h⟩ := h₄ b hb
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro k S
  let W := Fintype.piFinset (fun _ : Fin k => D)
  let v := fun w : Fin k → ℕ => ∑ i : Fin k, w i*b^(i:ℕ)
  have digits (w : Fin k → ℕ) (hw : w ∈ W) :
      v w < b^k ∧ ∀ i : Fin k, (v w/b^(i:ℕ)) % b = w i :=
    h₂ b k hb w (fun i => Finset.mem_range.mp (hDsub (Fintype.mem_piFinset.mp hw i)))
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
  have size : S.card = ∏ i : Fin k, D.card := by
    rw [← image, Finset.card_image_of_injOn inj]
    exact Fintype.card_piFinset _
  let R := S.filter (fun n : ℕ => Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ (Nat.dist p q)^3 ≤ n^2)
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
  rw [count, size, h₃ b k D R]
  exact le_trans (Complex.re_le_norm _) (h k D hDsub hDcard R (fun n hn => (Finset.mem_filter.mp hn).2))
