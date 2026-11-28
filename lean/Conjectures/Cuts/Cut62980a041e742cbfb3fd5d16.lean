import Mathlib

-- child 1 zh: 冻结裙边带 (wideArcs∖midArcs)∖(lowWideArcs∖arcs) 的'近心'部分（距有理中心 ≤ Q·n^{1/6}/(qn)）的积分实部最终下界 −εn。
-- child 1 en: Eventual -εn real-part floor on the near-centre ('inner') part of the frozen skirt band (distance to the rational ≤ Q·n^{1/6}/(qn)).
-- child 2 zh: 同一冻结裙边带的'远心'部分（近心半径之外的壳层）的整段积分范数最终上界 εn。
-- child 2 en: Eventual εn norm bound on the far-centre ('outer') shell of the same frozen skirt band (outside the inner radius).

theorem Conjectures.Cuts.Cut62980a041e742cbfb3fd5d16
    (h₁ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let band := fun n : ℕ => (wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n); let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (intervalIntegral (fun t => (band n ∩ inner n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re)
    (h₂ : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let band := fun n : ℕ => (wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n); let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖intervalIntegral (fun t => (band n \ inner n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume‖ ≤ e * (n : ℝ))
    : (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let remSkirt := fun n : ℕ => intervalIntegral (fun t => ((wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n)).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (remSkirt n).re) := by
  intro w E S Q arcs f Q₁ H midArcs wideArcs lowWideArcs remSkirt
  let band := fun n : ℕ => (wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n)
  let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}
  let I := fun (n : ℕ) (A : Set ℝ) => intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume
  let J := fun (n : ℕ) (A : Set ℝ) => (I n A).re
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ J n (band n ∩ inner n)) at h₁
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖I n (band n \ inner n)‖ ≤ e * (n : ℝ)) at h₂
  change ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ J n (band n)
  have hMeasGen (n D : ℕ) (R : ℝ) : MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ R / ((q : ℝ) * (n : ℝ))} := by
    have hset : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ R / ((q : ℝ) * (n : ℝ))} =
        ⋃ q : ℕ, ⋃ a : ℕ, {t : ℝ | 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q} ∩ {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ R / ((q : ℝ) * (n : ℝ))} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨q, a, hq, hD, ha, hc, ht⟩
        exact ⟨q, a, ⟨hq, hD, ha, hc⟩, ht⟩
      · rintro ⟨q, a, ⟨hq, hD, ha, hc⟩, ht⟩
        exact ⟨q, a, hq, hD, ha, hc, ht⟩
    rw [hset]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    exact (MeasurableSet.const _).inter (measurableSet_le (by fun_prop) (by fun_prop))
  have mArcs : ∀ n : ℕ, MeasurableSet (arcs n) := fun n => hMeasGen n (Q n) ((Q n : ℝ))
  have mMid : ∀ n : ℕ, MeasurableSet (midArcs n) := fun n => hMeasGen n (Q₁ n) ((Q n : ℝ))
  have mWide : ∀ n : ℕ, MeasurableSet (wideArcs n) := fun n => hMeasGen n (Q₁ n) ((H n : ℝ))
  have mLow : ∀ n : ℕ, MeasurableSet (lowWideArcs n) := fun n => hMeasGen n (Q n) ((H n : ℝ))
  have mInner : ∀ n : ℕ, MeasurableSet (inner n) := fun n => hMeasGen n (Q₁ n) ((Q n : ℝ) * (n : ℝ)^(1/6 : ℝ))
  have hAdd (n : ℕ) (X Y : Set ℝ) (hX : MeasurableSet X) (hY : MeasurableSet Y) (hdisj : Disjoint X Y) :
      J n (X ∪ Y) = J n X + J n Y := by
    have hf : Continuous (f n) := by
      simp only [f, S, E]
      fun_prop
    have hInt (U : Set ℝ) (hU : MeasurableSet U) :
        IntervalIntegrable (U.indicator (f n)) MeasureTheory.volume 0 1 := by
      have h := hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h ⊢
      exact h.indicator hU
    have hFun : (fun t => (X ∪ Y).indicator (f n) t) =
        fun t => X.indicator (f n) t + Y.indicator (f n) t := by
      funext t
      rw [Set.indicator_union_of_disjoint hdisj]
    unfold J I
    rw [hFun, intervalIntegral.integral_add (hInt X hX) (hInt Y hY), Complex.add_re]
  intro e he
  obtain ⟨N₁, hN₁⟩ := h₁ (e / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := h₂ (e / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn hEven => ?_⟩
  have mB : MeasurableSet (band n) := ((mWide n).diff (mMid n)).diff ((mLow n).diff (mArcs n))
  have mBinner : MeasurableSet (band n ∩ inner n) := mB.inter (mInner n)
  have mBout : MeasurableSet (band n \ inner n) := mB.diff (mInner n)
  have hpart : (band n ∩ inner n) ∪ (band n \ inner n) = band n := by
    ext t
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro ht
      by_cases h : t ∈ inner n
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
  have hdisj : Disjoint (band n ∩ inner n) (band n \ inner n) :=
    Set.disjoint_left.mpr fun _ ht ht' => ht'.2 ht.2
  have hadd := hAdd n (band n ∩ inner n) (band n \ inner n) mBinner mBout hdisj
  rw [hpart] at hadd
  have h₁n : -(e / 2 * (n : ℝ)) ≤ (I n (band n ∩ inner n)).re := by
    simpa only [J] using hN₁ n (by omega) hEven
  have h₂n : ‖I n (band n \ inner n)‖ ≤ e / 2 * (n : ℝ) := hN₂ n (by omega) hEven
  have hout : -(e / 2 * (n : ℝ)) ≤ (I n (band n \ inner n)).re := by
    have h0 : -(I n (band n \ inner n)).re ≤ ‖I n (band n \ inner n)‖ := by
      simpa using Complex.re_le_norm (-(I n (band n \ inner n)))
    linarith only [h0, h₂n]
  rw [hadd]
  simp only [J]
  linarith only [h₁n, hout]