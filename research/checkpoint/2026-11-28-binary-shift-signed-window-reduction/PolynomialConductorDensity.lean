import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli

/-! A polynomial-conductor specialization of the accepted zero-density
theorem. `V1 χ` lists nontrivial strip zeros of the primitive,
nonprincipal character χ with analytic multiplicity. -/

namespace Goldbach.PintzClasses
open OAI.Ostmann

/-- The density factor stays bounded on a strip of width K/log X when
both the conductor cutoff and the height are polynomial in X. -/
theorem polynomial_density_envelope {X d τ K q T : ℝ}
    (hX : 1 < X) (hK : 0 ≤ K)
    (hq : 1 ≤ q) (hT : 2 ≤ T) (hqX : q ≤ X^d) (hTX : T ≤ X^τ) :
    let σ := 1-K/Real.log X
    (q^2*T)^(3*(1-σ)/(2-σ)) * (Real.log (q*T))^13 ≤
      (Real.exp (3*(2*d+τ)*K) * (d+τ)^13) * (Real.log X)^13 := by
  intro σ
  have hx : 0 < X := zero_lt_one.trans hX
  have hl : 0 < Real.log X := Real.log_pos hX
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have ht0 : 0 < T := by linarith
  have hqlog : Real.log q ≤ d*Real.log X := by
    simpa only [Real.log_rpow hx] using Real.log_le_log hq0 hqX
  have htlog : Real.log T ≤ τ*Real.log X := by
    simpa only [Real.log_rpow hx] using Real.log_le_log ht0 hTX
  have hlogpair : Real.log (q*T) ≤ (d+τ)*Real.log X := by
    rw [Real.log_mul hq0.ne' ht0.ne']; linarith only [hqlog,htlog]
  have hbase : 1 ≤ q^2*T := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) (by linarith)
  have hlogbase : Real.log (q^2*T) ≤ (2*d+τ)*Real.log X := by
    rw [Real.log_mul (pow_ne_zero _ hq0.ne') ht0.ne', Real.log_pow]
    push_cast; linarith only [hqlog,htlog]
  have hs : 1-σ = K/Real.log X := by dsimp [σ]; ring
  have hden : 1 ≤ 2-σ := by
    dsimp [σ]; linarith [div_nonneg hK hl.le]
  have hex : 3*(1-σ)/(2-σ) ≤ 3*(K/Real.log X) := by
    rw [hs]; exact div_le_self (by positivity) hden
  have hpow : (q^2*T)^(3*(1-σ)/(2-σ)) ≤ Real.exp (3*(2*d+τ)*K) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hbase)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ Real.log (q^2*T) * (3*(K/Real.log X)) :=
        mul_le_mul_of_nonneg_left hex (Real.log_nonneg hbase)
      _ ≤ ((2*d+τ)*Real.log X) * (3*(K/Real.log X)) :=
        mul_le_mul_of_nonneg_right hlogbase (by positivity)
      _ = _ := by field_simp
  have hlogpos : 0 ≤ Real.log (q*T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  calc
    _ ≤ Real.exp (3*(2*d+τ)*K) * (((d+τ)*Real.log X)^13) :=
      mul_le_mul hpow (pow_le_pow_left₀ hlogpos hlogpair _) (pow_nonneg hlogpos _) (Real.exp_pos _).le
    _ = _ := by rw [mul_pow]; ring

/-- Absolute C is independent of d, τ and K. Each zero with
|Im ρ| ≤ T and 1-K/log X ≤ Re ρ < 1 is counted with multiplicity.
The character family is any finite set of primitive nonprincipal characters. -/
theorem polynomial_conductor_near_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (X d τ K T : ℝ) (Q : ℕ),
      1 < X → 0 ≤ d → 0 ≤ τ → 0 ≤ K → 2*K ≤ Real.log X →
      1 ≤ Q → 2 ≤ T → (Q:ℝ) ≤ X^d → T ≤ X^τ →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((V1 χ).count (1-K/Real.log X) T : ℝ)) ≤
        C*(Real.exp (3*(2*d+τ)*K)*(d+τ)^13)*(Real.log X)^13 := by
  obtain ⟨C,hC,hD⟩ := V1f0
  refine ⟨C,hC,?_⟩
  intro X d τ K T Q hX _hd _hτ hK hlarge hQ hT hqX hTX F hF
  have hl : 0 < Real.log X := Real.log_pos hX
  have hhalf : K/Real.log X ≤ 1/2 := (div_le_iff₀ hl).mpr (by linarith)
  have hdens := hD Q hQ T (1-K/Real.log X) hT (by linarith) (by linarith [div_nonneg hK hl.le]) F hF
  have hen := polynomial_density_envelope hX hK
    (by exact_mod_cast hQ : (1:ℝ) ≤ Q) hT hqX hTX
  calc
    _ ≤ _ := hdens
    _ = C * (((Q:ℝ)^2*T)^(3*(1-(1-K/Real.log X))/(2-(1-K/Real.log X))) * (Real.log ((Q:ℝ)*T))^13) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hen hC.le).trans_eq (by ring)

end Goldbach.PintzClasses

#print axioms Goldbach.PintzClasses.polynomial_conductor_near_one
