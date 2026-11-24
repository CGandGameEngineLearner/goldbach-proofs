import Mathlib

/-!
# L-goldbach-phase-variation

The total variation of a phase sequence at an offset `b` from an arc center is at most
`2πN|b|`: with `E x = exp (2πix)`, `∑ k < N, ‖E ((k+1)b) - E (kb)‖ ≤ 2π N |b|`.

Each summand is `‖E (kb)‖ · ‖E b - 1‖ = ‖E b - 1‖` because every phase has norm `1`, and a
chord is controlled by its arc length: `‖exp (I·θ) - 1‖ ≤ ‖θ‖`.  Summing the constant bound
`2π|b|` over `N` indices finishes the estimate.
-/

namespace PEqualNP.Outside.GoldbachPhaseVariationAux

/-- The phase map `x ↦ exp (2πix)`. -/
noncomputable def phaseE (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

theorem norm_phaseE (x : ℝ) : ‖phaseE x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Chord length is bounded by arc length. -/
theorem chord_le (x : ℝ) : ‖phaseE x - 1‖ ≤ 2*Real.pi*|x| := by
  have hE : phaseE x = Complex.exp (Complex.I * ((2*Real.pi*x:ℝ):ℂ)) := by
    unfold phaseE
    congr 1
    exact mul_comm _ _
  rw [hE]
  calc ‖Complex.exp (Complex.I * ((2*Real.pi*x:ℝ):ℂ)) - 1‖
      ≤ ‖(2*Real.pi*x:ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2*Real.pi*|x| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*Real.pi)]

/-- Every summand is bounded by the constant arc length `2π|b|`. -/
theorem term_le (k : ℕ) (b : ℝ) :
    ‖phaseE (((k:ℝ)+1)*b) - phaseE ((k:ℝ)*b)‖ ≤ 2*Real.pi*|b| := by
  have h1 : (((k:ℝ)+1)*b) = (k:ℝ)*b + b := by ring
  have h2 : phaseE ((k:ℝ)*b + b) = phaseE ((k:ℝ)*b) * phaseE b := by
    unfold phaseE
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h3 : phaseE ((k:ℝ)*b) * phaseE b - phaseE ((k:ℝ)*b)
      = phaseE ((k:ℝ)*b) * (phaseE b - 1) := by ring
  rw [h1, h2, h3, norm_mul, norm_phaseE, one_mul]
  exact chord_le b

theorem phase_variation_le (N : ℕ) (b : ℝ) :
    Finset.sum (Finset.range N) (fun k => ‖phaseE (((k:ℝ)+1)*b) - phaseE ((k:ℝ)*b)‖)
      ≤ 2*Real.pi*(N:ℝ)*|b| := by
  calc Finset.sum (Finset.range N) (fun k => ‖phaseE (((k:ℝ)+1)*b) - phaseE ((k:ℝ)*b)‖)
      ≤ Finset.sum (Finset.range N) (fun _ => 2*Real.pi*|b|) :=
        Finset.sum_le_sum (fun k _ => term_le k b)
    _ = (N:ℝ) * (2*Real.pi*|b|) := by simp
    _ = 2*Real.pi*(N:ℝ)*|b| := by ring

end PEqualNP.Outside.GoldbachPhaseVariationAux

theorem PEqualNP.Outside.L_goldbach_phase_variation :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (N : ℕ) (b : ℝ), Finset.sum (Finset.range N) (fun k => ‖E (((k:ℝ)+1)*b)-E ((k:ℝ)*b)‖) ≤ 2*Real.pi*(N:ℝ)*|b| :=
  fun N b => PEqualNP.Outside.GoldbachPhaseVariationAux.phase_variation_le N b
