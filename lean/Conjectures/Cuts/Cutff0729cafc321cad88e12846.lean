import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli
import Conjectures.Goldbach.WideSignedRemainderBridge

-- 前提里保留了完整的 let 链（与父题的记号逐字对齐），其中部分 let 绑定在单个前提内
-- 未被显式引用，属预期情况；由此产生的 unused variables linter warning 无需处理。

-- child 1 zh: 低模主弧裙边带（q ≤ (log₂ n)²、半径扩至 H/(qn)，去掉原始主弧）的积分实部
--            在更强预算 −(e/2)n 下有无条件下界，e 任意小。
-- child 1 en: Stronger-budget -((e)/2)n unconditional floor on the low-modulus skirt
--            (q ≤ (log₂ n)², radius widened to H/(qn), original major arcs removed).
-- child 2 zh: 扩宽剩余弧区里“近有理”(inner) 部分的积分实部在更强预算 −(e/3)n 下有无条件下界。
-- child 2 en: Stronger-budget -((e)/3)n unconditional floor on the near-rational (inner) part
--            of the widened remainder.
-- child 3 zh: 扩宽剩余弧区里“远有理”(outer) 部分的积分实部在更强预算 −(e/4)n 下有无条件下界。
-- child 3 en: Stronger-budget -((e)/4)n unconditional floor on the far (outer) part of the
--            widened remainder.
--
-- 归约思路 / reduction strategy (independent of Cut #4115, which splits the whole region with
-- three equal -e/3 budgets and goes through the bridge's own set-splitting lemma):
--   * 各自实例化 / instantiate the three premises at e' = e/2 (each premise carries its own
--     stronger coefficient): 得到 -(e/2·e'/e)n = -(e/4)n ≤ J(lowPart)，同理
--     -(e/3·e'/e)n = -(e/6)n ≤ J(inner part)，-(e/4·e'/e)n = -(e/8)n ≤ J(outer part)。
--   * 加法合并 / add up: 系数满足 (e/2+e/3+e/4)·(e'/e) = 13/24·e ≤ e，
--     于是 -((e/2/2 + e/2/3 + e/2/4))n ≤ J(lowPart)+J(inner)+J(outer)。
--   * 集合拆分 / set split: 直接展开 J 的定义，用 indicator 的加法性（不交并上的
--     indicator = indicator 之和）证明整段积分 = 三部分积分之和，再 nlinarith/linarith。
--   因此不需要调用 WideSignedRemainderBridge（它在内部恰好也是这三步，并把预算三等分
--   成 -e/3 n），这里只保留对它的导入以便与父题的记号/接口保持一致。

theorem Conjectures.Cuts.Cutff0729cafc321cad88e12846
    (h₁ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e/2 * (n:ℝ)) ≤ J n (A n); floor (fun n => lowWideArcs n \ arcs n))
    (h₂ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e/3 * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n ∩ inner n))
    (h₃ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e/4 * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n \ inner n)) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => wideArcs n \ arcs n)) := by
  have cutMeas : ∀ (X : ℕ) (ρ n : ℝ),
      MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)} := by
    intro X ρ n
    have h : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}
        = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q} ∩ {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}) := by
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

  have cutAdd : ∀ (g : ℝ → ℂ), Continuous g → ∀ (B C : Set ℝ),
      MeasurableSet B → MeasurableSet C → Disjoint B C →
      (intervalIntegral (fun t => (B ∪ C).indicator g t) (0:ℝ) 1 MeasureTheory.volume).re =
        (intervalIntegral (fun t => B.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re +
        (intervalIntegral (fun t => C.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re := by
    intro g hg B C hB hC hd
    have hi : ∀ D : Set ℝ, MeasurableSet D →
        IntervalIntegrable (fun t => D.indicator g t) MeasureTheory.volume 0 1 := by
      intro D hD
      have := (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this ⊢
      exact this.indicator hD
    have : (fun t => (B ∪ C).indicator g t) = fun t => B.indicator g t + C.indicator g t := by
      funext t
      rw [Set.indicator_union_of_disjoint hd]
    rw [this, intervalIntegral.integral_add (hi B hB) (hi C hC), Complex.add_re]

  have cutPow : ∀ (L : ℕ), 40 ≤ L → L ^ 6 + 2 ≤ 2 ^ L := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base => norm_num
    | succ L hL ih =>
      have h1 : 10 * (L + 1) ≤ 11 * L := by omega
      have h2 : (10 * (L + 1)) ^ 6 ≤ (11 * L) ^ 6 := Nat.pow_le_pow_left h1 6
      have h3 : 10 ^ 6 * (L + 1) ^ 6 ≤ 2 * 10 ^ 6 * L ^ 6 := by
        calc 10 ^ 6 * (L + 1) ^ 6 = (10 * (L + 1)) ^ 6 := by ring
          _ ≤ (11 * L) ^ 6 := h2
          _ = 11 ^ 6 * L ^ 6 := by ring
          _ ≤ 2 * 10 ^ 6 * L ^ 6 := by
            apply Nat.mul_le_mul_right; norm_num
      have h4 : (L + 1) ^ 6 ≤ 2 * L ^ 6 := by
        have : 10 ^ 6 * (L + 1) ^ 6 ≤ 10 ^ 6 * (2 * L ^ 6) := by nlinarith
        exact Nat.le_of_mul_le_mul_left this (by norm_num)
      have h5 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
      omega

  have cutEv : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Nat.log 2 (n+2))^2 ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := by
    refine ⟨2 ^ 40, fun n hn => ?_⟩
    have hl : 40 ≤ Nat.log 2 (n+2) := by
      apply Nat.le_log_of_pow_le (by norm_num)
      omega
    have hp := cutPow _ hl
    have hq : 2 ^ Nat.log 2 (n+2) ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
    have h6 : (Nat.log 2 (n+2)) ^ 6 ≤ n := by omega
    apply Nat.le_floor
    have h6' : (((Nat.log 2 (n+2))^2 : ℕ) : ℝ) ^ 3 ≤ (n:ℝ) := by
      have : (((Nat.log 2 (n+2))^2 : ℕ) : ℝ) ^ 3 = (((Nat.log 2 (n+2))^6 : ℕ) : ℝ) := by
        push_cast; ring
      rw [this]; exact_mod_cast h6
    have h0 : (0:ℝ) ≤ (((Nat.log 2 (n+2))^2 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (((Nat.log 2 (n+2))^2 : ℕ) : ℝ)
        = ((((Nat.log 2 (n+2))^2 : ℕ) : ℝ) ^ 3) ^ (1/3:ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
      _ ≤ (n:ℝ) ^ (1/3:ℝ) := Real.rpow_le_rpow (by positivity) h6' (by norm_num)

  intro w E S Q arcs f Q₁ H wideArcs lowWideArcs lowPart remainder inner J floor e he
  obtain ⟨N₀, hN₀⟩ := cutEv
  -- 三个前提都在 e' = e/2 处实例化，得到更小的预算 e/4, e/6, e/8。
  obtain ⟨N₁, k₁⟩ := h₁ (e/2) (by linarith)
  obtain ⟨N₂, k₂⟩ := h₂ (e/2) (by linarith)
  obtain ⟨N₃, k₃⟩ := h₃ (e/2) (by linarith)
  refine ⟨max N₀ (max N₁ (max N₂ N₃)), fun n hn hev => ?_⟩
  have a₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have a₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have a₂ : N₂ ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have a₃ : N₃ ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have hcont : Continuous (f n) := by
    simp only [f, S, E]
    fun_prop
  -- 低模裙边带落在扩宽带内，只要 Q n ≤ Q₁ n。
  have hsub : lowWideArcs n \ arcs n ⊆ wideArcs n \ arcs n := by
    rintro t ⟨ht, hna⟩
    obtain ⟨q, a, h₁', h₂', h₃', h₄', h₅'⟩ := ht
    exact ⟨⟨q, a, h₁', le_trans h₂' (hN₀ n a₀), h₃', h₄', h₅'⟩, hna⟩
  have mW : MeasurableSet (wideArcs n) := cutMeas (Q₁ n) (H n : ℝ) (n:ℝ)
  have mA : MeasurableSet (arcs n) := cutMeas (Q n) (Q n : ℝ) (n:ℝ)
  have mLw : MeasurableSet (lowWideArcs n) := cutMeas (Q n) (H n : ℝ) (n:ℝ)
  have mI : MeasurableSet (inner n) :=
    cutMeas (Q₁ n) ((Q n : ℝ) * (n:ℝ)^(1/6:ℝ)) (n:ℝ)
  set X := wideArcs n \ arcs n with hX
  set L := lowWideArcs n \ arcs n with hLd
  have mX : MeasurableSet X := mW.diff mA
  have mL : MeasurableSet L := mLw.diff mA
  have hLX : L ⊆ X := by rw [hLd, hX]; exact hsub
  have mR : MeasurableSet (X \ L) := mX.diff mL
  have mRI : MeasurableSet (X \ L ∩ inner n) := mR.inter mI
  have mRJ : MeasurableSet ((X \ L) \ inner n) := mR.diff mI
  -- 集合恒等式：X 是不交并 L ∪ ((X\L)∩I) ∪ ((X\L)\I)。
  have e1 : X = L ∪ ((X \ L ∩ inner n) ∪ ((X \ L) \ inner n)) := by
    rw [Set.inter_union_sdiff, Set.union_sdiff_cancel hLX]
  have d1 : Disjoint (X \ L ∩ inner n) ((X \ L) \ inner n) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact ht'.2 ht.2
  have d2 : Disjoint L ((X \ L ∩ inner n) ∪ ((X \ L) \ inner n)) := by
    rw [Set.inter_union_sdiff]
    exact Set.disjoint_sdiff_right
  -- 展开 J 的定义后，用 indicator 的可加性把整段积分拆成三部分之和。
  have key : J n X = J n L + (J n (X \ L ∩ inner n) + J n ((X \ L) \ inner n)) := by
    have hJd : ∀ A : Set ℝ,
        J n A = (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re :=
      fun A => rfl
    rw [hJd, hJd, hJd, hJd]
    conv_lhs => rw [e1]
    rw [cutAdd (f n) hcont _ _ mL (mRI.union mRJ) d2, cutAdd (f n) hcont _ _ mRI mRJ d1]
  rw [key]
  have b₁ : -(((e/2)/2) * (n:ℝ)) ≤ J n L := k₁ n a₁ hev
  have b₂ : -(((e/2)/3) * (n:ℝ)) ≤ J n (X \ L ∩ inner n) := k₂ n a₂ hev
  have b₃ : -(((e/2)/4) * (n:ℝ)) ≤ J n ((X \ L) \ inner n) := k₃ n a₃ hev
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hcoef : e/2/2 + e/2/3 + e/2/4 ≤ e := by linarith
  have hmul : (e/2/2 + e/2/3 + e/2/4) * (n:ℝ) ≤ e * (n:ℝ) :=
    mul_le_mul_of_nonneg_right hcoef hn0
  have hsum : -((e/2/2 + e/2/3 + e/2/4) * (n:ℝ)) ≤
      J n L + (J n (X \ L ∩ inner n) + J n ((X \ L) \ inner n)) := by
    nlinarith [b₁, b₂, b₃]
  linarith [hsum, hmul]
