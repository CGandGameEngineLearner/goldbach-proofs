import Mathlib

theorem PEqualNP.Outside.L_goldbach_frontier_master_zone_bridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let medCore := fun n : ℕ => intervalIntegral (fun t => (midArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let medSkirt := fun n : ℕ => intervalIntegral (fun t => (wideArcs n \ midArcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let deepMinor := fun n : ℕ => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → minor n = (medCore n + medSkirt n) + deepMinor n) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (medCore n + medSkirt n).re) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (deepMinor n).re) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (minor n).re := by

  intro w E S Q arcs f minor Q1 H midArcs wideArcs medCore medSkirt deepMinor hsplit hmed hdeep e he
  obtain ⟨N0, hN0⟩ := hsplit
  have he2 : 0 < e / 2 := by linarith
  obtain ⟨N1, hN1⟩ := hmed (e / 2) he2
  obtain ⟨N2, hN2⟩ := hdeep (e / 2) he2
  refine ⟨max (max N0 N1) N2, ?_⟩
  intro n hn heven
  have hn0 : N0 ≤ n := le_trans (le_trans (le_max_left N0 N1) (le_max_left (max N0 N1) N2)) hn
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_right N0 N1) (le_max_left (max N0 N1) N2)) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right (max N0 N1) N2) hn
  have hmed' : -(e / 2 * (n : ℝ)) ≤ (medCore n).re + (medSkirt n).re := by
    have h := hN1 n hn1 heven
    rw [Complex.add_re] at h
    exact h
  have hdeep' : -(e / 2 * (n : ℝ)) ≤ (deepMinor n).re := hN2 n hn2 heven
  rw [hN0 n hn0]
  have hre : ((medCore n + medSkirt n) + deepMinor n).re
      = (medCore n).re + (medSkirt n).re + (deepMinor n).re := by
    rw [Complex.add_re, Complex.add_re]
  rw [hre]
  have heq : -(e * (n : ℝ)) = -(e / 2 * (n : ℝ)) + -(e / 2 * (n : ℝ)) := by ring
  linarith
