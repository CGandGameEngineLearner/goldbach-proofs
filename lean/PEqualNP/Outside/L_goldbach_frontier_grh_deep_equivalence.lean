import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

theorem L_goldbach_frontier_grh_deep_equivalence :
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) → let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let medCore := fun n : ℕ => intervalIntegral (fun t => (midArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let medSkirt := fun n : ℕ => intervalIntegral (fun t => (wideArcs n \ midArcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let deepMinor := fun n : ℕ => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → minor n = (medCore n + medSkirt n) + deepMinor n) → ((∀ (Q₀ : ℕ) [NeZero Q₀] (χ : DirichletCharacter ℂ Q₀) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (medCore n + medSkirt n).re) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (deepMinor n).re) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (minor n).re := by
  intro GRH
  dsimp only
  intro hsplit hAB hDeep e he
  obtain ⟨N₀, hN₀⟩ := hsplit
  obtain ⟨N₁, hN₁⟩ := hAB GRH (e / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hDeep (e / 2) (by linarith)
  refine ⟨max N₀ (max N₁ N₂), fun n hn hEven => ?_⟩
  have hN0le : N₀ ≤ n := le_trans (le_max_left N₀ (max N₁ N₂)) hn
  have hN1le : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_right N₀ (max N₁ N₂))) hn
  have hN2le : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_right N₀ (max N₁ N₂))) hn
  have h0 := hN₀ n hN0le
  have h1 := hN₁ n hN1le hEven
  have h2 := hN₂ n hN2le hEven
  rw [h0, Complex.add_re]
  have hkey : -(e * (n : ℝ)) = -(e / 2 * (n : ℝ)) + -(e / 2 * (n : ℝ)) := by ring
  linarith [h1, h2, hkey]

end PEqualNP.Outside
