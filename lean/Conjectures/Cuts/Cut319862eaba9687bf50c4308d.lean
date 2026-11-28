import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment

open MeasureTheory Filter

-- child 1 zh: 对原宽弧之外、平方根模数弧之内的对角系数证明单侧 o(n) 下界。
-- child 1 en: Prove a one-sided o(n) floor on the diagonal coefficient in the square-root arcs outside the original wide arcs.
-- child 2 zh: 对平方根模数弧与原宽弧的并集之外的对角系数证明单侧 o(n) 下界。
-- child 2 en: Prove a one-sided o(n) floor on the diagonal coefficient outside both rational-arc families.
theorem Conjectures.Cuts.Cut319862eaba9687bf50c4308d (h₁ :
    let weight (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0
    let phase (t : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * t) * Complex.I)
    let primeSum (n : ℕ) (t : ℝ) : ℂ :=
      ∑ k ∈ Finset.range (n+1), ↑(weight k) * phase ((k : ℝ) * t)
    let integrand (n m : ℕ) (t : ℝ) : ℂ := primeSum n t ^ 2 * phase (-(m : ℝ) * t)
    let arcs (qmax n : ℕ) : Set ℝ :=
      {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ qmax ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a : ℝ) / q| ≤ ((256 * qmax * Nat.log 2 (n+2)^2 : ℕ) : ℝ) / ((q : ℝ) * n)}
    let wide (n : ℕ) : Set ℝ := arcs ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊ n
    let extended (n : ℕ) : Set ℝ :=
      arcs ⌊Real.sqrt (n : ℝ) / (↑(Nat.log 2 (n+2)) : ℝ)^4⌋₊ n
    let coeff (A : Set ℝ) (n m : ℕ) : ℂ := ∫ t in (0 : ℝ)..1, A.indicator (integrand n m) t
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
      -(ε * (n : ℝ)) ≤ (coeff (extended n \ wide n) n n).re) (h₂ :
    let weight (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0
    let phase (t : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * t) * Complex.I)
    let primeSum (n : ℕ) (t : ℝ) : ℂ :=
      ∑ k ∈ Finset.range (n+1), ↑(weight k) * phase ((k : ℝ) * t)
    let integrand (n m : ℕ) (t : ℝ) : ℂ := primeSum n t ^ 2 * phase (-(m : ℝ) * t)
    let arcs (qmax n : ℕ) : Set ℝ :=
      {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ qmax ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a : ℝ) / q| ≤ ((256 * qmax * Nat.log 2 (n+2)^2 : ℕ) : ℝ) / ((q : ℝ) * n)}
    let wide (n : ℕ) : Set ℝ := arcs ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊ n
    let extended (n : ℕ) : Set ℝ :=
      arcs ⌊Real.sqrt (n : ℝ) / (↑(Nat.log 2 (n+2)) : ℝ)^4⌋₊ n
    let coeff (A : Set ℝ) (n m : ℕ) : ℂ := ∫ t in (0 : ℝ)..1, A.indicator (integrand n m) t
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
      -(ε * (n : ℝ)) ≤ (coeff ((extended n ∪ wide n)ᶜ) n n).re) : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℝ) => ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x1 x5) : ℂ) * x2 ((↑x5 : ℝ) * x4); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → ℕ := fun (x5 : ℕ) => ⌊(↑x5 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x6 : ℕ → ℕ := fun (x6 : ℕ) => (256 : ℕ) * x5 x6 * x4 x6; have x7 : ℕ → Set ℝ := fun (x7 : ℕ) => {x8 : ℝ | ∃ (x9 : ℕ) (x10 : ℕ), (1 : ℕ) ≤ x9 ∧ x9 ≤ x5 x7 ∧ x10 ≤ x9 ∧ x10.Coprime x9 ∧ |x8 - (↑x10 : ℝ) / (↑x9 : ℝ)| ≤ (↑(x6 x7) : ℝ) / ((↑x9 : ℝ) * (↑x7 : ℝ))}; have x8 : ℕ → ℕ → ℝ := fun (x8 x9 : ℕ) => (∫ (x10 : ℝ) in (0 : ℝ)..(1 : ℝ), (x7 x8)ᶜ.indicator (fun (x11 : ℝ) => x3 x8 x11 ^ (2 : ℕ) * x2 (-(↑x9 : ℝ) * x11)) x10).re; ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℕ), ∀ x12 ≥ x11, Even x12 → (1 : ℝ) / ((↑x12 : ℝ) + (1 : ℝ)) * ∑ x15 ∈ Finset.Icc x12 ((2 : ℕ) * x12), x8 x12 x15 - x9 / (2 : ℝ) * (↑x12 : ℝ) ≤ x8 x12 x12) := by
  let weight (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0
  let phase (t : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * t) * Complex.I)
  let primeSum (n : ℕ) (t : ℝ) : ℂ :=
    ∑ k ∈ Finset.range (n+1), ↑(weight k) * phase ((k : ℝ) * t)
  let integrand (n m : ℕ) (t : ℝ) : ℂ := primeSum n t ^ 2 * phase (-(m : ℝ) * t)
  let arcs (qmax n : ℕ) : Set ℝ :=
    {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ qmax ∧ a ≤ q ∧ a.Coprime q ∧
      |t - (a : ℝ) / q| ≤ ((256 * qmax * Nat.log 2 (n+2)^2 : ℕ) : ℝ) / ((q : ℝ) * n)}
  let wide (n : ℕ) : Set ℝ := arcs ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊ n
  let extended (n : ℕ) : Set ℝ :=
    arcs ⌊Real.sqrt (n : ℝ) / (↑(Nat.log 2 (n+2)) : ℝ)^4⌋₊ n
  let shell (b : Bool) (n : ℕ) : Set ℝ :=
    if b then extended n \ wide n else (extended n ∪ wide n)ᶜ
  let coeff (A : Set ℝ) (n m : ℕ) : ℂ := ∫ t in (0 : ℝ)..1, A.indicator (integrand n m) t
  let ShellFloor (b : Bool) : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
      -(ε * (n : ℝ)) ≤ (coeff (shell b n) n n).re

  have measurableShell (b : Bool) (n : ℕ) : MeasurableSet (shell b n) := by
    have hw : MeasurableSet (wide n) := EffectiveArcEndpoint.frontierMeasurable _ _ _
    have hx : MeasurableSet (extended n) := EffectiveArcEndpoint.frontierMeasurable _ _ _
    cases b
    · exact (hx.union hw).compl
    · exact hx.diff hw

  have splitCoeff (n : ℕ) :
      coeff (wide n)ᶜ n n = coeff (shell true n) n n + coeff (shell false n) n n := by
    have hc : Continuous (integrand n n) := by
      unfold integrand primeSum phase
      fun_prop
    have hi : IntervalIntegrable (integrand n n) volume 0 1 := hc.intervalIntegrable 0 1
    have hint (b : Bool) : IntervalIntegrable ((shell b n).indicator (integrand n n)) volume 0 1 :=
      intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp hi).indicator (measurableShell b n))
    unfold coeff
    rw [← intervalIntegral.integral_add (hint true) (hint false)]
    apply congrArg (fun f : ℝ → ℂ => ∫ t in (0 : ℝ)..1, f t)
    funext t
    by_cases hw : t ∈ wide n <;> by_cases he : t ∈ extended n <;>
      simp [shell, Set.indicator, hw, he]

  have meanBound (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
      (1 : ℝ) / ((n : ℝ)+1) * ∑ m ∈ Finset.Icc n (2*n), (coeff (wide n)ᶜ n m).re ≤
        ε * (n : ℝ) := by
    obtain ⟨K, hK⟩ := PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment
      (1/6) (by norm_num)
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/6 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/6)).comp tendsto_natCast_atTop_atTop
    obtain ⟨L, hL⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop (1/(ε^2)))
    refine ⟨max (max K L) 1, fun n hn => ?_⟩
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hNp : 0 < (n : ℝ)+1 := by positivity
    have hscale : (1 : ℝ) ≤ ε^2 * (n : ℝ) ^ (1/6 : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < ε^2)).mp (hL n (by omega))
    have heq : (n : ℝ)^((8/3 : ℝ)+1/6) * (n : ℝ)^(1/6 : ℝ) = (n : ℝ)^3 := by
      rw [← Real.rpow_add hn0, show (8/3 : ℝ)+1/6+1/6 = 3 by norm_num]
      exact Real.rpow_natCast _ 3
    have hpow := mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hn0.le ((8/3 : ℝ)+1/6))
    rw [mul_one, ← mul_left_comm, heq] at hpow
    let u (m : ℕ) : ℝ := (coeff (wide n)ᶜ n m).re
    let I := Finset.Icc n (2*n)
    have hmoment : ∑ m ∈ I, ‖coeff (wide n)ᶜ n m‖^2 ≤ (n : ℝ)^((8/3 : ℝ)+1/6) :=
      hK n (by omega)
    have hu : ∑ m ∈ I, u m ^ 2 ≤ (n : ℝ)^((8/3 : ℝ)+1/6) := by
      refine (Finset.sum_le_sum fun m _ => ?_).trans hmoment
      rw [← sq_abs (u m)]
      exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) _
    have hcard : (I.card : ℝ) = (n : ℝ)+1 := by
      have h : I.card = n+1 := by dsimp [I]; rw [Nat.card_Icc]; omega
      exact_mod_cast h
    have hsq : (∑ m ∈ I, u m)^2 ≤ (ε * (n : ℝ) * ((n : ℝ)+1))^2 := by
      calc
        _ ≤ (I.card : ℝ) * ∑ m ∈ I, u m^2 := sq_sum_le_card_mul_sum_sq
        _ ≤ ((n : ℝ)+1) * (ε^2 * (n : ℝ)^3) := by
          rw [hcard]
          exact mul_le_mul_of_nonneg_left (hu.trans hpow) hNp.le
        _ ≤ _ := by
          have hx : 0 ≤ ε^2 * (n : ℝ)^2 * ((n : ℝ)+1) := by positivity
          nlinarith only [hx]
    have hbound := abs_le_of_sq_le_sq hsq (by positivity)
    have hh : (∑ m ∈ I, u m) ≤ ε * (n : ℝ) * ((n : ℝ)+1) :=
      (le_abs_self _).trans (hbound.elim le_of_lt le_of_eq)
    change 1 / ((n : ℝ)+1) * (∑ m ∈ I, u m) ≤ ε * (n : ℝ)
    rw [one_div, ← div_eq_inv_mul]
    exact (div_le_iff₀ hNp).mpr hh
  dsimp only
  intro ε hε
  obtain ⟨M, hM⟩ := meanBound (ε/4) (by positivity)
  change ShellFloor true at h₁
  change ShellFloor false at h₂
  obtain ⟨N₁, hN₁⟩ := h₁ (ε/8) (by positivity)
  obtain ⟨N₂, hN₂⟩ := h₂ (ε/8) (by positivity)
  refine ⟨max M (max N₁ N₂), fun n hn hen => ?_⟩
  change (1 : ℝ) / ((n : ℝ)+1) * ∑ m ∈ Finset.Icc n (2*n), (coeff (wide n)ᶜ n m).re -
    ε / 2 * (n : ℝ) ≤ (coeff (wide n)ᶜ n n).re
  have hm := hM n (by omega)
  have h1 := hN₁ n (by omega) hen
  have h2 := hN₂ n (by omega) hen
  rw [splitCoeff, Complex.add_re]
  linarith only [hm, h1, h2]
