import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_frontier_medium_assembly_bridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let medCore := fun n : ℕ => intervalIntegral (fun t => (midArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let medSkirt := fun n : ℕ => intervalIntegral (fun t => (wideArcs n \ midArcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Qqp := fun n : ℕ => ⌊Real.exp (Real.sqrt (Real.log (n:ℝ)))⌋₊; let Qzf := fun n : ℕ => ⌊(n:ℝ)^(1/10:ℝ)⌋₊; let K := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.range (n+1), E ((k:ℝ)*β); let medCoreBand := fun (n A B : ℕ) => intervalIntegral (fun t => {u : ℝ | ∃ q a : ℕ, A < q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧ |u - (a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let modelBand := fun (n A B : ℕ) => ∑ q ∈ Finset.Ioc A B, ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), intervalIntegral (fun t => (((∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r:ℝ)*(a:ℝ)/(q:ℝ))) / (Nat.totient q : ℂ)) * K n (t - (a:ℝ)/(q:ℝ)))^2 * E (-(n:ℝ)*t)) ((a:ℝ)/(q:ℝ) - (Q n:ℝ)/((q:ℝ)*(n:ℝ))) ((a:ℝ)/(q:ℝ) + (Q n:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let remSkirt := fun n : ℕ => intervalIntegral (fun t => ((wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n)).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → medCore n = medCoreBand n (Q n) (Qqp n) + medCoreBand n (Qqp n) (Qzf n) + medCoreBand n (Qzf n) (Q₁ n) ∧ modelBand n (Q n) (Q₁ n) = modelBand n (Q n) (Qqp n) + modelBand n (Qqp n) (Qzf n) + modelBand n (Qzf n) (Q₁ n) ∧ medSkirt n = lowSkirt n + remSkirt n) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (modelBand n (Q n) (Q₁ n)).re) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Q n) (Qqp n) - modelBand n (Q n) (Qqp n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Qqp n) (Qzf n) - modelBand n (Qqp n) (Qzf n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Qzf n) (Q₁ n) - modelBand n (Qzf n) (Q₁ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (remSkirt n).re) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (medCore n + medSkirt n).re := by
  intro w E S Q arcs f Q₁ H midArcs wideArcs medCore medSkirt Qqp Qzf K
    medCoreBand modelBand lowWideArcs lowSkirt remSkirt
    hsplit hmodel herror1 herror2 herror3 hlow hrem e he
  have he6 : (0 : ℝ) < e / 6 := div_pos he (by norm_num)
  obtain ⟨N0, hsplit⟩ := hsplit
  obtain ⟨N1, hmodel⟩ := hmodel (e / 6) he6
  obtain ⟨N2, herror1⟩ := herror1 (e / 6) he6
  obtain ⟨N3, herror2⟩ := herror2 (e / 6) he6
  obtain ⟨N4, herror3⟩ := herror3 (e / 6) he6
  obtain ⟨N5, hlow⟩ := hlow (e / 6) he6
  obtain ⟨N6, hrem⟩ := hrem (e / 6) he6
  refine ⟨max N0 (max N1 (max N2 (max N3 (max N4 (max N5 N6))))), ?_⟩
  intro n hn heven
  rcases max_le_iff.mp hn with ⟨hn0, ht1⟩
  rcases max_le_iff.mp ht1 with ⟨hn1, ht2⟩
  rcases max_le_iff.mp ht2 with ⟨hn2, ht3⟩
  rcases max_le_iff.mp ht3 with ⟨hn3, ht4⟩
  rcases max_le_iff.mp ht4 with ⟨hn4, ht5⟩
  rcases max_le_iff.mp ht5 with ⟨hn5, hn6⟩
  rcases hsplit n hn0 with ⟨hcore, hmodels, hskirt⟩
  have hm := hmodel n hn1 heven
  have hl := hlow n hn5 heven
  have hr := hrem n hn6 heven
  have herr1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (herror1 n hn2 heven))).1
  have herr2 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (herror2 n hn3 heven))).1
  have herr3 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (herror3 n hn4 heven))).1
  simp only [Complex.sub_re] at herr1 herr2 herr3
  have hmodel_re := congrArg Complex.re hmodels
  simp only [Complex.add_re] at hmodel_re
  rw [Complex.add_re, hcore, hskirt]
  simp only [Complex.add_re]
  nlinarith only [hm, hl, hr, herr1, herr2, herr3, hmodel_re]
