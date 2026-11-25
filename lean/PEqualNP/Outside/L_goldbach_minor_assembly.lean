import Mathlib

/-!
# Assembling the minor-arc bounds into the signed floor

`main` splits the minor-arc coefficient into low-low, low-high and high-high
(`minor-bilinear-split`), proves the first two are absolutely `o(n)`
(`small-small-saving`, `small-bulk-saving`), and leaves the one-sided bound on
the high-high piece open (`bulk-signed-floor`).

This file supplies the missing implication: those four statements together give
the target `arc-minor-saving`. There is no analysis in it. The content is that
the constants add up (`1/8 + 1/4 + 1/2 < 1`) and that the real part of a
complex number is bounded below by minus its norm.

The analytic input is a hypothesis, exactly as in
`L-goldbach-exception-dyadic-bound`.
-/

namespace PEqualNP.Outside

noncomputable def gW : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k:ℝ) else 0

noncomputable def gE : ℝ → ℂ := fun x => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

noncomputable def gS (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*gE ((k:ℝ)*t))

noncomputable def gQ (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

def gArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤gQ n ∧ a≤q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (gQ n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def gLow (n k : ℕ) : ℝ := if k^3≤n then gW k else 0

noncomputable def gHigh (n k : ℕ) : ℝ := gW k - gLow n k

noncomputable def gI (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral (fun t => (gArcs n)ᶜ.indicator (fun u => gS n a u*gS n b u*gE (-(n:ℝ)*u)) t)
    (0:ℝ) 1 MeasureTheory.volume

noncomputable def gMinor (n : ℕ) : ℂ :=
  intervalIntegral (fun t => (gArcs n)ᶜ.indicator (fun t => (gS n gW t)^2*gE (-(n:ℝ)*t)) t)
    (0:ℝ) 1 MeasureTheory.volume

/-- Bookkeeping core: the split plus the three bounds give the signed floor. -/
theorem minor_assembly_core :
    ∀ (e : ℝ), 0 < e → ∀ n : ℕ, Even n →
      gI n gW gW = gI n (gLow n) (gLow n) + 2 * gI n (gLow n) (gHigh n)
        + gI n (gHigh n) (gHigh n) →
      ‖gI n (gLow n) (gLow n)‖ ≤ e*(n:ℝ)/8 →
      ‖gI n (gLow n) (gHigh n)‖ ≤ e*(n:ℝ)/8 →
      -(e*(n:ℝ)/2) ≤ (gI n (gHigh n) (gHigh n)).re →
      -(e*(n:ℝ)) ≤ (gMinor n).re := by
  intro e he n _hn hsplit h1 h2 h3
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hen : (0:ℝ) ≤ e*(n:ℝ) := mul_nonneg he.le hn0
  have hm : gMinor n = gI n gW gW := by
    simp only [gMinor, gI, pow_two]
  have hkey : ∀ z : ℂ, -(‖z‖) ≤ z.re := by
    intro z
    have h := Complex.re_le_norm (-z)
    simp only [Complex.neg_re, norm_neg] at h
    linarith
  have hLL : -(e*(n:ℝ)/8) ≤ (gI n (gLow n) (gLow n)).re := by
    have := hkey (gI n (gLow n) (gLow n))
    linarith
  have hLH : -(e*(n:ℝ)/4) ≤ 2 * (gI n (gLow n) (gHigh n)).re := by
    have := hkey (gI n (gLow n) (gHigh n))
    linarith
  have hre : (gI n (gLow n) (gLow n) + 2 * gI n (gLow n) (gHigh n)
      + gI n (gHigh n) (gHigh n)).re
      = (gI n (gLow n) (gLow n)).re + 2 * (gI n (gLow n) (gHigh n)).re
        + (gI n (gHigh n) (gHigh n)).re := by
    simp [Complex.add_re, Complex.mul_re]
  rw [hm, hsplit, hre]
  linarith

/-- The four published pieces imply the signed floor on the whole minor arc. -/
theorem L_goldbach_minor_assembly : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun t => (S n w t)^2*E (-(n:ℝ)*t)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ (e : ℝ), 0 < e → ∀ n : ℕ, Even n → I n w w = I n (low n) (low n) + 2 * I n (low n) (high n) + I n (high n) (high n) → ‖I n (low n) (low n)‖ ≤ e*(n:ℝ)/8 → ‖I n (low n) (high n)‖ ≤ e*(n:ℝ)/8 → -(e*(n:ℝ)/2) ≤ (I n (high n) (high n)).re → -(e*(n:ℝ)) ≤ (minor n).re := by
  exact minor_assembly_core

end PEqualNP.Outside
