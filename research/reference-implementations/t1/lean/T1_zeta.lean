import PrimeNumberTheoremAnd.StrongPNT

/-!
# 由 PNT+ 的 `StrongPNT` 得到「ζ 版 T1」

`StrongPNT : ∃ c > 0, (ChebyshevPsi - id) =O[atTop] fun x => x * exp(-c * √(log x))`
是 `IsBigO`，而 `T1` 是存在量化的（`∃ C c X`），所以 **Big-O 足够**。
本文件把它展开成显式常数 + 显式阈值的形状。
-/

open Asymptotics Filter

/-- **ζ 版 T1**：`∃ C c X, ∀ x ≥ X, |ψ x − x| ≤ C·x·exp(−c√(log x))`。 -/
theorem psi_classical_error :
    ∃ (C c X : ℝ), 0 < C ∧ 0 < c ∧ 0 < X ∧
      ∀ x : ℝ, X ≤ x →
        |ChebyshevPsi x - x| ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x))) := by
  obtain ⟨c, hc, hO⟩ := StrongPNT
  obtain ⟨C₀, hC₀⟩ := isBigO_iff.mp hO
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hC₀
  refine ⟨|C₀| + 1, c, max X₁ 2, by positivity, hc, by positivity, ?_⟩
  intro x hx
  have hxX : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : ‖ChebyshevPsi x - x‖
      ≤ C₀ * ‖x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 2))‖ := by
    have h := hX₁ x hxX
    simpa only [Pi.sub_apply, id_eq] using h
  have hg : ‖x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 2))‖
      = x * Real.exp (-(c * Real.sqrt (Real.log x))) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx0, abs_of_pos (Real.exp_pos _)]
    congr 2
    rw [← Real.sqrt_eq_rpow]
    ring
  rw [hg, Real.norm_eq_abs] at h1
  have hC₀le : C₀ ≤ |C₀| + 1 := by
    have := le_abs_self C₀
    linarith
  have hnonneg : 0 ≤ x * Real.exp (-(c * Real.sqrt (Real.log x))) := by positivity
  calc |ChebyshevPsi x - x|
      ≤ C₀ * (x * Real.exp (-(c * Real.sqrt (Real.log x)))) := h1
    _ ≤ (|C₀| + 1) * (x * Real.exp (-(c * Real.sqrt (Real.log x)))) :=
        mul_le_mul_of_nonneg_right hC₀le hnonneg
    _ = (|C₀| + 1) * x * Real.exp (-(c * Real.sqrt (Real.log x))) := by ring
