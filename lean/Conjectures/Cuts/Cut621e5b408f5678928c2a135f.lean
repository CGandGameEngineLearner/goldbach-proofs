import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli
import Conjectures.Goldbach.WideSignedRemainderBridge

-- 父目标 T n = remainder n ∩ inner n 二分 / two-way split of the parent target:
--   A n = T n ∩ lowWideArcs n   （落在扩宽低模裙边带内的那部分）
--   B n = T n \ lowWideArcs n  （落在扩宽低模裙边带外的那部分）
--   A n ∪ B n = T n，A n 与 B n 不交，预算 e/2 + e/2 = e。
-- 两个 child 都是与父题同一条 let 链下的 floor，预算更强（e/2），故可独立假定。
-- 归约只用到 indicator 在测集上的可加性（局部 have cutMeas / cutAdd），不调用
-- WideSignedRemainderBridge（其内部待证的正是父命题，会循环）。

-- child 1 zh: 父目标中落入扩宽低模裙边带的部分 A n = T n ∩ lowWideArcs n 的积分实部，
--            在更强预算 −(e/2)n 下有无条件单侧下界，e 任意小。
-- child 1 en: Stronger-budget -((e/2)n) unconditional floor on the part of the parent
--            target that lies inside the widened low-modulus skirt.
-- child 2 zh: 父目标中落在扩宽低模裙边带之外的部分 B n = T n \ lowWideArcs n 的积分实部，
--            在更强预算 −(e/2)n 下有无条件单侧下界，e 任意小。
-- child 2 en: Stronger-budget -((e/2)n) unconditional floor on the part of the parent
--            target that lies outside the widened low-modulus skirt.

theorem Conjectures.Cuts.Cut621e5b408f5678928c2a135f
    (h₁ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -((e/2) * (n:ℝ)) ≤ J n (A n); floor (fun n => (remainder n ∩ inner n) ∩ lowWideArcs n))
    (h₂ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -((e/2) * (n:ℝ)) ≤ J n (A n); floor (fun n => (remainder n ∩ inner n) \ lowWideArcs n)) :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n ∩ inner n) := by
  intro w E S Q arcs f Q₁ H wideArcs lowWideArcs lowPart remainder inner J floor e he
  obtain ⟨N₁, k₁⟩ := h₁ e he
  obtain ⟨N₂, k₂⟩ := h₂ e he
  refine ⟨max N₁ N₂, fun n hn hev => ?_⟩
  have a₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have a₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  -- 局部 helper：这类弧集可测。
  have cutMeas : ∀ (X : ℕ) (ρ n : ℝ),
      MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)} := by
    intro X ρ n
    have h : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧
          |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}
        = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q} ∩
          {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
        exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨q, a, h1, h2, h3, h4, h5⟩
    rw [h]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    refine (MeasurableSet.const _).inter ?_
    exact measurableSet_le (by fun_prop) (by fun_prop)
  -- 局部 helper：不交并上 indicator 积分的实部可加。
  have cutAdd : ∀ (g : ℝ → ℂ), Continuous g → ∀ (P R : Set ℝ),
      MeasurableSet P → MeasurableSet R → Disjoint P R →
      (intervalIntegral (fun t => (P ∪ R).indicator g t) (0:ℝ) 1 MeasureTheory.volume).re =
        (intervalIntegral (fun t => P.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re +
        (intervalIntegral (fun t => R.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re := by
    intro g hg P R hP hR hd
    have hi : ∀ D : Set ℝ, MeasurableSet D →
        IntervalIntegrable (fun t => D.indicator g t) MeasureTheory.volume 0 1 := by
      intro D hD
      have h0 := hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h0 ⊢
      exact h0.indicator hD
    have hfun : (fun t => (P ∪ R).indicator g t) = fun t => P.indicator g t + R.indicator g t := by
      funext t
      rw [Set.indicator_union_of_disjoint hd]
    rw [hfun, intervalIntegral.integral_add (hi P hP) (hi R hR), Complex.add_re]
  -- 连续性（供 cutAdd 使用）。
  have hcont : Continuous (f n) := by
    simp only [f, S, E]
    fun_prop
  -- 可测性：wideArcs / arcs / lowWideArcs / inner 都是同型弧集。
  have mW : MeasurableSet (wideArcs n) := cutMeas (Q₁ n) (H n : ℝ) (n:ℝ)
  have mAr : MeasurableSet (arcs n) := cutMeas (Q n) (Q n : ℝ) (n:ℝ)
  have mLw : MeasurableSet (lowWideArcs n) := cutMeas (Q n) (H n : ℝ) (n:ℝ)
  have mI : MeasurableSet (inner n) :=
    cutMeas (Q₁ n) ((Q n : ℝ) * (n:ℝ)^(1/6:ℝ)) (n:ℝ)
  have mLp : MeasurableSet (lowPart n) := mLw.diff mAr
  have mR : MeasurableSet (remainder n) := (mW.diff mAr).diff mLp
  have mT : MeasurableSet (remainder n ∩ inner n) := mR.inter mI
  have mP : MeasurableSet ((remainder n ∩ inner n) ∩ lowWideArcs n) := mT.inter mLw
  have mQ : MeasurableSet ((remainder n ∩ inner n) \ lowWideArcs n) := mT.diff mLw
  -- 二分：T = A ∪ B，两半不交。
  have e1 : remainder n ∩ inner n =
      ((remainder n ∩ inner n) ∩ lowWideArcs n) ∪
        ((remainder n ∩ inner n) \ lowWideArcs n) := by
    rw [Set.inter_union_sdiff]
  have d1 : Disjoint ((remainder n ∩ inner n) ∩ lowWideArcs n)
      ((remainder n ∩ inner n) \ lowWideArcs n) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact ht'.2 ht.2
  -- J 在二分上是可加的。
  have key : J n (remainder n ∩ inner n) =
      J n ((remainder n ∩ inner n) ∩ lowWideArcs n) +
        J n ((remainder n ∩ inner n) \ lowWideArcs n) := by
    have hJd : ∀ A : Set ℝ,
        J n A = (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re :=
      fun A => rfl
    rw [hJd, hJd, hJd]
    conv_lhs => rw [e1]
    rw [cutAdd (f n) hcont _ _ mP mQ d1]
  have b₁ : -((e/2) * (n:ℝ)) ≤ J n ((remainder n ∩ inner n) ∩ lowWideArcs n) :=
    k₁ n a₁ hev
  have b₂ : -((e/2) * (n:ℝ)) ≤ J n ((remainder n ∩ inner n) \ lowWideArcs n) :=
    k₂ n a₂ hev
  -- 预算相加：e/2 + e/2 = e。
  have hcoef : e/2 + e/2 = e := by ring
  linarith [key, b₁, b₂, hcoef]
