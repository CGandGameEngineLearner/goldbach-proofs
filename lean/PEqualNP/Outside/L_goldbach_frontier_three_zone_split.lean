import Mathlib

namespace GoldbachAux

/-! ### Arithmetic: 64*L^6 <= 2^L for L >= 40 -/

theorem pow_six_le_two_pow (L : ℕ) : 40 ≤ L → 64 * L ^ 6 ≤ 2 ^ L := by
  induction L with
  | zero => intro h; omega
  | succ L ih =>
    intro hL
    rcases Nat.lt_or_ge L 40 with hLt | hGe
    · have hL1 : L + 1 = 40 := by omega
      rw [hL1]; norm_num
    · have hpos : 0 < L := by omega
      have ih' := ih hGe
      have hL4 : L ^ 3 ≤ L ^ 4 := Nat.pow_le_pow_right hpos (by omega)
      have hL2c : L ^ 2 ≤ L ^ 4 := Nat.pow_le_pow_right hpos (by omega)
      have hL1c : L ≤ L ^ 4 := by
        calc L = L ^ 1 := (Nat.pow_one L).symm
          _ ≤ L ^ 4 := Nat.pow_le_pow_right hpos (by omega)
      have hL0c : 1 ≤ L ^ 4 := Nat.one_le_pow 4 L hpos
      have hB : 40 * L ^ 4 ≤ L ^ 5 := by
        calc L ^ 5 = L ^ 4 * L := Nat.pow_succ L 4
          _ ≥ L ^ 4 * 40 := Nat.mul_le_mul_left _ (by omega)
          _ = 40 * L ^ 4 := Nat.mul_comm _ _
      have hA : 40 * L ^ 5 ≤ L ^ 6 := by
        calc L ^ 6 = L ^ 5 * L := Nat.pow_succ L 5
          _ ≥ L ^ 5 * 40 := Nat.mul_le_mul_left _ (by omega)
          _ = 40 * L ^ 5 := Nat.mul_comm _ _
      have h57 : 57 * L ^ 4 ≤ 2 * L ^ 5 := by linarith
      have hex : (L + 1) ^ 6 = L ^ 6 + 6 * L ^ 5 + 15 * L ^ 4 + 20 * L ^ 3 + 15 * L ^ 2 + 6 * L + 1 := by ring
      have hexp : (L + 1) ^ 6 ≤ 2 * L ^ 6 := by
        rw [hex]; linarith
      calc 64 * (L + 1) ^ 6 ≤ 64 * (2 * L ^ 6) := Nat.mul_le_mul_left 64 hexp
        _ = 2 * (64 * L ^ 6) := by ring
        _ ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 ih'
        _ = 2 ^ (L + 1) := by rw [Nat.pow_succ]; ring

/-! ### Real cube-root bound -/

theorem rpow_third_ge {a b : ℝ} (ha : 0 ≤ a) (h : a ^ 3 ≤ b) : a ≤ b ^ (1/3:ℝ) := by
  have h2 : a ^ (3:ℝ) = a ^ 3 := Real.rpow_natCast a 3
  have h1 : a = (a ^ 3) ^ (1/3:ℝ) := by
    rw [← h2, ← Real.rpow_mul ha, show (3:ℝ) * (1/3:ℝ) = 1 by ring, Real.rpow_one]
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) h (by positivity)

theorem log_sq_le_rpow_third (n : ℕ) (hn : 2 ^ 40 ≤ n) :
    ((Nat.log2 (n+2))^2 : ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by
  norm_num at hn
  have hn0 : n ≠ 0 := by omega
  have hL40 : 40 ≤ Nat.log2 n := (Nat.le_log2 hn0).mpr hn
  have hLle : 2 ^ (Nat.log2 n) ≤ n := (Nat.le_log2 hn0).mp le_rfl
  have hLt : n < 2 ^ (Nat.log2 n + 1) := by
    by_contra h
    push_neg at h
    have h' := (Nat.le_log2 hn0).mpr h
    omega
  have h64n : 64 * (Nat.log2 n) ^ 6 ≤ n := (pow_six_le_two_pow _ hL40).trans hLle
  have hcube : (4:ℝ) * (Nat.log2 n)^2 ≤ (n:ℝ)^(1/3:ℝ) := by
    have h2 : ((4:ℝ) * (Nat.log2 n)^2)^3 ≤ (n:ℝ) := by
      have h1 : ((4:ℝ) * (Nat.log2 n)^2)^3 = 64 * (Nat.log2 n)^6 := by push_cast; ring
      rw [h1]; exact_mod_cast h64n
    exact rpow_third_ge (by positivity) h2
  have hlog : Nat.log2 (n+2) ≤ Nat.log2 n + 1 := by
    by_contra h
    have h' : Nat.log2 n + 2 ≤ Nat.log2 (n+2) := by omega
    have h2le : 2 ^ (Nat.log2 n + 2) ≤ n + 2 := (Nat.le_log2 (by omega)).mp h'
    have h22 : 2 ^ (Nat.log2 n + 2) = 2 * 2 ^ (Nat.log2 n + 1) := by
      rw [Nat.pow_succ, Nat.pow_succ]; ring
    have h2pos : 2 ≤ 2 ^ (Nat.log2 n + 1) := by
      have h := Nat.one_lt_two_pow (n := Nat.log2 n + 1) (by omega)
      omega
    omega
  have hsq : (Nat.log2 (n+2))^2 ≤ 4 * (Nat.log2 n)^2 := by
    have h1 : (Nat.log2 (n+2))^2 ≤ (Nat.log2 n + 1)^2 := Nat.pow_le_pow_left hlog 2
    have h2 : (Nat.log2 n + 1)^2 ≤ 4 * (Nat.log2 n)^2 := by nlinarith
    exact h1.trans h2
  calc ((Nat.log2 (n+2))^2 : ℝ) ≤ (4:ℝ) * (Nat.log2 n)^2 := by exact_mod_cast hsq
    _ ≤ (n:ℝ)^(1/3:ℝ) := hcube

theorem log_sq_le_floor_third (n : ℕ) (hn : 2 ^ 40 ≤ n) :
    (Nat.log2 (n+2))^2 ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := by
  rw [← Nat.floor_natCast (R := ℝ) ((Nat.log2 (n+2))^2)]
  exact Nat.floor_le_floor (by push_cast; exact log_sq_le_rpow_third n hn)

/-! ### Measurability of the arc sets -/

theorem measurable_arcSet (Qmax R n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qmax ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} := by
  have hball : ∀ (q a : ℕ), MeasurableSet {t : ℝ | Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} := by
    intro q a
    by_cases h : Nat.Coprime a q
    · have heq : {t : ℝ | Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} = {t : ℝ | |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} := by
        ext t
        constructor
        · rintro ⟨-, h5⟩; exact h5
        · intro h5; exact ⟨h, h5⟩
      rw [heq]
      exact (isClosed_le (continuous_abs.comp (continuous_sub_right _)) continuous_const).measurableSet
    · have heq : {t : ℝ | Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} = (∅ : Set ℝ) := by
        ext t
        constructor
        · rintro ⟨hc, -⟩; exact absurd hc h
        · intro h5; simp at h5
      rw [heq]; exact MeasurableSet.empty
  have hset : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qmax ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))}
      = ⋃ q ∈ Finset.Ico 1 (Qmax + 1), ⋃ a ∈ Finset.Ico 0 (q + 1), {t : ℝ | Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Ico]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, ⟨h1, Nat.lt_succ_of_le h2⟩, a, ⟨Nat.zero_le a, Nat.lt_succ_of_le h3⟩, ⟨h4, h5⟩⟩
    · rintro ⟨q, hq, a, ha, h45⟩
      exact ⟨q, a, hq.1, Nat.lt_succ_iff.mp hq.2, Nat.lt_succ_iff.mp ha.2, h45.1, h45.2⟩
  have hc1 : {b : ℕ | b ∈ Finset.Ico 1 (Qmax + 1)}.Countable := Finset.countable_toSet (Finset.Ico 1 (Qmax + 1))
  rw [hset]
  exact MeasurableSet.biUnion hc1 (fun q _ =>
    MeasurableSet.biUnion (Finset.countable_toSet (Finset.Ico 0 (q + 1))) (fun a _ => hball q a))

/-! ### Integral three-zone splitting -/

theorem intervalIntegrable_indicator {f : ℝ → ℂ} {s : Set ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume 0 1 :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

theorem split_identity (f : ℝ → ℂ) (A B C : Set ℝ) (hAB : A ⊆ B) (hBC : B ⊆ C)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    intervalIntegral (fun t => Aᶜ.indicator f t) 0 1 MeasureTheory.volume =
      (intervalIntegral (fun t => (B \ A).indicator f t) 0 1 MeasureTheory.volume +
       intervalIntegral (fun t => (C \ B).indicator f t) 0 1 MeasureTheory.volume) +
      intervalIntegral (fun t => Cᶜ.indicator f t) 0 1 MeasureTheory.volume := by
  have h1 : IntervalIntegrable (fun t => (B \ A).indicator f t) MeasureTheory.volume 0 1 :=
    intervalIntegrable_indicator hf (hB.diff hA)
  have h2 : IntervalIntegrable (fun t => (C \ B).indicator f t) MeasureTheory.volume 0 1 :=
    intervalIntegrable_indicator hf (hC.diff hB)
  have h3 : IntervalIntegrable (fun t => Cᶜ.indicator f t) MeasureTheory.volume 0 1 :=
    intervalIntegrable_indicator hf hC.compl
  have h12 : IntervalIntegrable (fun t => (B \ A).indicator f t + (C \ B).indicator f t) MeasureTheory.volume 0 1 :=
    h1.add h2
  have hpt : Set.EqOn (fun t => Aᶜ.indicator f t)
      (fun t => (B \ A).indicator f t + (C \ B).indicator f t + Cᶜ.indicator f t) (Set.uIcc (0:ℝ) 1) := by
    intro t _
    by_cases ha : t ∈ A
    · have hb : t ∈ B := hAB ha
      have hc : t ∈ C := hBC hb
      simp [Set.indicator_apply, Set.mem_compl_iff, Set.mem_diff, ha, hb, hc]
    · by_cases hb : t ∈ B
      · have hc : t ∈ C := hBC hb
        simp [Set.indicator_apply, Set.mem_compl_iff, Set.mem_diff, ha, hb, hc]
      · by_cases hc : t ∈ C
        · simp [Set.indicator_apply, Set.mem_compl_iff, Set.mem_diff, ha, hb, hc]
        · simp [Set.indicator_apply, Set.mem_compl_iff, Set.mem_diff, ha, hb, hc]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add h12 h3,
    intervalIntegral.integral_add h1 h2]

/-! ### Continuity of the integrand -/

theorem continuous_E : Continuous (fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) := by
  refine Complex.continuous_exp.comp ?_
  fun_prop

theorem continuous_S (n : ℕ) (u : ℕ → ℝ) :
    Continuous (fun t : ℝ => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))) := by
  refine continuous_finsetSum _ (fun k _ => ?_)
  exact continuous_const.mul (continuous_E.comp (continuous_const.mul continuous_id))

theorem continuous_f (n : ℕ) :
    Continuous (fun t : ℝ => (Finset.sum (Finset.range (n+1)) (fun k => ((if Nat.Prime k then Real.log (k:ℝ) else 0 : ℝ):ℂ)*Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)))^2 * Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I)) := by
  exact ((continuous_S n (fun k => if Nat.Prime k then Real.log (k:ℝ) else 0)).pow 2).mul
    (continuous_E.comp (continuous_const.mul continuous_id))

end GoldbachAux

theorem PEqualNP.Outside.L_goldbach_frontier_three_zone_split : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let medCore := fun n : ℕ => intervalIntegral (fun t => (midArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let medSkirt := fun n : ℕ => intervalIntegral (fun t => (wideArcs n \ midArcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let deepMinor := fun n : ℕ => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → minor n = (medCore n + medSkirt n) + deepMinor n := by
  refine ⟨2 ^ 40, fun n hn => ?_⟩
  norm_num at hn
  have hn1 : 1 ≤ n := by omega
  have hQQ : (Nat.log 2 (n+2))^2 ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := by
    rw [← Nat.log2_eq_log_two]
    exact GoldbachAux.log_sq_le_floor_third n hn
  refine GoldbachAux.split_identity _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Set.mem_setOf_eq] at ht ⊢
    obtain ⟨q, a, h1, h2, h3, h4, h5⟩ := ht
    exact ⟨q, a, h1, h2.trans hQQ, h3, h4, h5⟩
  · intro t ht
    simp only [Set.mem_setOf_eq] at ht ⊢
    obtain ⟨q, a, h1, h2, h3, h4, h5⟩ := ht
    refine ⟨q, a, h1, h2, h3, h4, ?_⟩
    have hQ1pos : 0 < ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := by
      have hf1 : (1:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by
        have h : (1:ℝ)^(1/3:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn1) (by positivity)
        rwa [Real.one_rpow] at h
      have h := (Nat.one_le_floor_iff _).mpr hf1
      omega
    have hpos : 0 < 256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := Nat.mul_pos (by norm_num) hQ1pos
    have hQH : (Nat.log 2 (n+2))^2 ≤ 256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ * (Nat.log 2 (n+2))^2 := by
      have h1 := Nat.le_mul_of_pos_right ((Nat.log 2 (n+2))^2) hpos
      calc (Nat.log 2 (n+2))^2 ≤ (Nat.log 2 (n+2))^2 * (256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊) := h1
        _ = 256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ * (Nat.log 2 (n+2))^2 := by ring
    have hQHr : (((Nat.log 2 (n+2))^2 : ℕ) : ℝ) ≤ ((256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ * (Nat.log 2 (n+2))^2 : ℕ) : ℝ) := by
      exact_mod_cast hQH
    have hnq : 0 < (q:ℝ)*(n:ℝ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
    exact h5.trans ((div_le_div_iff_of_pos_right hnq).mpr hQHr)
  · exact GoldbachAux.measurable_arcSet _ _ _
  · exact GoldbachAux.measurable_arcSet _ _ _
  · exact GoldbachAux.measurable_arcSet _ _ _
  · exact (GoldbachAux.continuous_f n).intervalIntegrable 0 1
