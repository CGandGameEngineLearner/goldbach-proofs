import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_strip_geometry_inverse_square_tail :
    ∀ (S : Finset ℂ) (T : ℝ), 0<T → (∀ z ∈ S,T≤|z.im|) → Finset.sum S (fun z => ‖z⁻¹‖^2) ≤ (S.card:ℝ)/T^2 := by
  intro S T hT hheight
  have hterm : ∀ z ∈ S, ‖z⁻¹‖ ^ 2 ≤ (1 / T) ^ 2 := by
    intro z hz
    have him : T ≤ ‖z‖ := by
      calc
        T ≤ |z.im| := hheight z hz
        _ ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hnorm : ‖z⁻¹‖ ≤ 1 / T := by
      rw [norm_inv]
      have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hT him
      rw [div_le_iff₀ hT]
      simpa [one_mul] using him
    exact sq_le_sq₀ (norm_nonneg _) hnorm
  calc
    Finset.sum S (fun z => ‖z⁻¹‖ ^ 2)
        ≤ Finset.sum S (fun _ => (1 / T) ^ 2) :=
      Finset.sum_le_sum (fun z hz => hterm z hz)
    _ = (S.card : ℝ) * (1 / T) ^ 2 := by simp
    _ = (S.card : ℝ) / T ^ 2 := by field_simp

end PEqualNP.Outside
