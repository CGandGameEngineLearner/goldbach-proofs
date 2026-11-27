import Mathlib

noncomputable section

open MeasureTheory

namespace Conjectures.Goldbach.WideSignedRemainderBridge_aux

private lemma six_le_two_pow (k : ℕ) (hk : 30 ≤ k) : k ^ 6 + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hratio : (k : ℝ) ≥ 30 := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by linarith
    have h1R : ((k : ℝ) + 1) ^ 6 ≤ 2 * (k : ℝ) ^ 6 := by
      have hquot : ((k : ℝ) + 1) / (k : ℝ) ≤ 11 / 10 := by
        rw [div_le_iff₀ hkpos]
        linarith
      have hpow : (((k : ℝ) + 1) / (k : ℝ)) ^ 6 ≤ ((11 : ℝ) / 10) ^ 6 :=
        pow_le_pow_left₀ (by positivity) hquot 6
      have h2 : ((11 : ℝ) / 10) ^ 6 ≤ 2 := by norm_num
      have hkey : (((k : ℝ) + 1) ^ 6) / (k : ℝ) ^ 6 ≤ 2 := by
        rw [← div_pow]
        exact hpow.trans h2
      have := mul_le_mul_of_nonneg_right hkey (pow_nonneg hkpos.le 6)
      rwa [div_mul_cancel₀ _ (pow_ne_zero 6 hkpos.ne')] at this
    have h1 : (k + 1) ^ 6 ≤ 2 * k ^ 6 := by
      have h1R' : ((k : ℝ) + 1) ^ 6 ≤ 2 * (k : ℝ) ^ 6 := h1R
      exact_mod_cast h1R'
    calc (k + 1) ^ 6 + 2 ≤ 2 * k ^ 6 + 2 := by omega
      _ ≤ 2 * (k ^ 6 + 2) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

private lemma cube_le_floor (n Q : ℕ) (h : Q ^ 3 ≤ n) :
    Q ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
  have hR : (Q : ℝ) ^ 3 ≤ (n : ℝ) := by exact_mod_cast h
  have hpow : (((Q : ℝ)) ^ 3) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hR (by norm_num)
  have hQid : (((Q : ℝ)) ^ 3) ^ (1 / 3 : ℝ) = (Q : ℝ) := by
    rw [← Real.rpow_natCast (x := (Q : ℝ)) 3]
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  rw [hQid] at hpow
  exact Nat.le_floor hpow

private lemma logSquare_le_cubeRootFloor (n : ℕ) (hn : 2 ^ 30 ≤ n) :
    (Nat.log 2 (n + 2)) ^ 2 ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
  have hk30 : 30 ≤ Nat.log 2 (n + 2) := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    omega
  have hk6 : (Nat.log 2 (n + 2)) ^ 6 ≤ n := by
    have h1 : (Nat.log 2 (n + 2)) ^ 6 + 2 ≤ 2 ^ (Nat.log 2 (n + 2)) :=
      six_le_two_pow (Nat.log 2 (n + 2)) hk30
    have h2 : 2 ^ (Nat.log 2 (n + 2)) ≤ n + 2 :=
      Nat.pow_log_le_self 2 (by omega)
    omega
  have hcube : ((Nat.log 2 (n + 2)) ^ 2) ^ 3 ≤ n := by
    have hpow : ((Nat.log 2 (n + 2)) ^ 2) ^ 3 = (Nat.log 2 (n + 2)) ^ 6 := by ring
    rw [hpow]
    exact hk6
  exact cube_le_floor n ((Nat.log 2 (n + 2)) ^ 2) hcube

private lemma shell_arcs_measurable (n D : ℕ) (R : ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ R / ((q : ℝ) * (n : ℝ))} := by
  have hEq : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ R / ((q : ℝ) * (n : ℝ))} =
      ⋃ (p : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ D ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1}),
        {t : ℝ | |t - (p.1.2 : ℝ) / (p.1.1 : ℝ)| ≤
          R / ((p.1.1 : ℝ) * (n : ℝ))} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨⟨(q, a), h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨⟨⟨q, a⟩, h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [hEq]
  exact MeasurableSet.iUnion (fun _ =>
    (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet)

private lemma indicator_three_remainder (D A I : Set ℝ) (g : ℝ → ℂ)
    (hAD : A ⊆ D) (t : ℝ) :
    D.indicator g t =
      (A.indicator g t + ((D \ A) ∩ I).indicator g t) +
        ((D \ A) \ I).indicator g t := by
  classical
  by_cases hD : t ∈ D
  · by_cases hA : t ∈ A
    · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hD, hA]
    · by_cases hI : t ∈ I
      · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hD, hA, hI]
      · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hD, hA, hI]
  · have hA : t ∉ A := fun hA => hD (hAD hA)
    simp [Set.indicator_of_notMem, hD, hA]

private lemma intervalIntegral_three_remainder (D A I : Set ℝ) (g : ℝ → ℂ)
    (hAD : A ⊆ D) (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hI : MeasurableSet I) (hg : Continuous g) :
    intervalIntegral (fun t => D.indicator g t) (0 : ℝ) 1 volume =
      (intervalIntegral (fun t => A.indicator g t) (0 : ℝ) 1 volume +
        intervalIntegral (fun t => ((D \ A) ∩ I).indicator g t) (0 : ℝ) 1 volume) +
          intervalIntegral (fun t => ((D \ A) \ I).indicator g t) (0 : ℝ) 1 volume := by
  have hgInt : IntervalIntegrable g volume (0 : ℝ) 1 := hg.intervalIntegrable 0 1
  have hint (s : Set ℝ) (hs : MeasurableSet s) :
      IntervalIntegrable (fun t => s.indicator g t) volume (0 : ℝ) 1 :=
    ⟨hgInt.1.indicator hs, hgInt.2.indicator hs⟩
  have hRem : MeasurableSet (D \ A) := hD.diff hA
  have hAint := hint A hA
  have hNearInt := hint ((D \ A) ∩ I) (hRem.inter hI)
  have hFarInt := hint ((D \ A) \ I) (hRem.diff hI)
  calc
    intervalIntegral (fun t => D.indicator g t) (0 : ℝ) 1 volume =
        intervalIntegral
          (fun t => (A.indicator g t + ((D \ A) ∩ I).indicator g t) +
            ((D \ A) \ I).indicator g t) (0 : ℝ) 1 volume := by
              apply intervalIntegral.integral_congr
              intro t _
              exact indicator_three_remainder D A I g hAD t
    _ = intervalIntegral
          (fun t => A.indicator g t + ((D \ A) ∩ I).indicator g t) (0 : ℝ) 1 volume +
        intervalIntegral (fun t => ((D \ A) \ I).indicator g t) (0 : ℝ) 1 volume :=
      intervalIntegral.integral_add (hAint.add hNearInt) hFarInt
    _ = (intervalIntegral (fun t => A.indicator g t) (0 : ℝ) 1 volume +
          intervalIntegral (fun t => ((D \ A) ∩ I).indicator g t) (0 : ℝ) 1 volume) +
        intervalIntegral (fun t => ((D \ A) \ I).indicator g t) (0 : ℝ) 1 volume := by
      rw [intervalIntegral.integral_add hAint hNearInt]

end Conjectures.Goldbach.WideSignedRemainderBridge_aux

theorem Conjectures.Goldbach.WideSignedRemainderBridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor lowPart → (floor (fun n => remainder n ∩ inner n)) → (floor (fun n => remainder n \ inner n)) → (floor (fun n => wideArcs n \ arcs n)) := by
  intro w E S Q arcs f Q₁ H wideArcs lowWideArcs lowPart remainder inner J floor
    hLowFloor hNearFloor hFarFloor e he
  obtain ⟨NLow, hLow⟩ := hLowFloor (e / 3) (by linarith)
  obtain ⟨NNear, hNear⟩ := hNearFloor (e / 3) (by linarith)
  obtain ⟨NFar, hFar⟩ := hFarFloor (e / 3) (by linarith)
  refine ⟨max (2 ^ 30) (max NLow (max NNear NFar)), ?_⟩
  intro n hn hEven
  have hnGeo : 2 ^ 30 ≤ n := (le_max_left _ _).trans hn
  have hnRest : max NLow (max NNear NFar) ≤ n := (le_max_right _ _).trans hn
  have hnLow : NLow ≤ n := (le_max_left _ _).trans hnRest
  have hnNearFar : max NNear NFar ≤ n := (le_max_right _ _).trans hnRest
  have hnNear : NNear ≤ n := (le_max_left _ _).trans hnNearFar
  have hnFar : NFar ≤ n := (le_max_right _ _).trans hnNearFar
  have hQle : Q n ≤ Q₁ n := by
    exact Conjectures.Goldbach.WideSignedRemainderBridge_aux.logSquare_le_cubeRootFloor n hnGeo
  have hLowSubset : lowPart n ⊆ wideArcs n \ arcs n := by
    intro t ht
    change t ∈ lowWideArcs n \ arcs n at ht
    change t ∈ wideArcs n \ arcs n
    rcases ht with ⟨htLow, htArcs⟩
    rcases htLow with ⟨q, a, hq, hqQ, ha, hcop, hradius⟩
    exact ⟨⟨q, a, hq, hqQ.trans hQle, ha, hcop, hradius⟩, htArcs⟩
  have hmArcs : MeasurableSet (arcs n) :=
    Conjectures.Goldbach.WideSignedRemainderBridge_aux.shell_arcs_measurable n (Q n) (Q n : ℝ)
  have hmWide : MeasurableSet (wideArcs n) :=
    Conjectures.Goldbach.WideSignedRemainderBridge_aux.shell_arcs_measurable n (Q₁ n) (H n : ℝ)
  have hmLowWide : MeasurableSet (lowWideArcs n) :=
    Conjectures.Goldbach.WideSignedRemainderBridge_aux.shell_arcs_measurable n (Q n) (H n : ℝ)
  have hmInner : MeasurableSet (inner n) :=
    Conjectures.Goldbach.WideSignedRemainderBridge_aux.shell_arcs_measurable n (Q₁ n)
      ((Q n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ))
  have hf : Continuous (f n) := by
    dsimp only [f, S, E]
    fun_prop
  have hIntegral :=
    Conjectures.Goldbach.WideSignedRemainderBridge_aux.intervalIntegral_three_remainder
      (wideArcs n \ arcs n) (lowPart n) (inner n) (f n) hLowSubset
      (hmWide.diff hmArcs) (hmLowWide.diff hmArcs) hmInner hf
  have hJsplit :
      J n (wideArcs n \ arcs n) =
        (J n (lowPart n) + J n (remainder n ∩ inner n)) +
          J n (remainder n \ inner n) := by
    simpa only [J, remainder, Complex.add_re] using congrArg Complex.re hIntegral
  have hLow' := hLow n hnLow hEven
  have hNear' := hNear n hnNear hEven
  have hFar' := hFar n hnFar hEven
  rw [hJsplit]
  linarith
