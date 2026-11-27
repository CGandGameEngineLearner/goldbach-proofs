import Mathlib
import Conjectures.Goldbach.DynExceptionEnergy

theorem Conjectures.Goldbach.BeaumontCentralPredictionTransfer :
    let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p =>
      p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n)
    let M := fun X : ℕ => (X:ℝ)/(Real.log (X:ℝ))^2
    let R := fun n : ℕ => ((H n + H (n+2)):ℝ)
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∃ b : ℕ → ℝ,
      (∀ n ∈ E X, M X ≤ b n) ∧
      (∑ n ∈ E X, (R n-b n)^2) ≤ ε*(X:ℝ)*(M X)^2) →
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (((Finset.Icc X (2*X)).filter (fun n => Even n ∧ H n=0 ∧ H (n+2)=0)).card:ℝ) ≤
        ε*(X:ℝ)) := by
  intro H E M R predict ε hε
  obtain ⟨N, hN⟩ := predict ε hε
  refine ⟨max 2 N, ?_⟩
  intro X hX
  have hlarge : 2 ≤ X := (le_max_left ..).trans hX
  obtain ⟨b, hfloor, herror⟩ := hN X ((le_max_right ..).trans hX)
  have hX' : (1:ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hM : 0 < M X := div_pos (by linarith) (sq_pos_of_pos (Real.log_pos hX'))
  have hset : (Finset.Icc X (2*X)).filter (fun n => Even n ∧ H n=0 ∧ H (n+2)=0) =
      (E X).filter (fun n => R n = 0) := by
    ext n
    simp [E, R, ← Nat.cast_add, and_assoc]
  rw [hset]
  exact (le_of_mul_le_mul_right
    ((Conjectures.Goldbach.DynExceptionEnergy (E X) R b (M X) hM hfloor).trans herror)
    (sq_pos_of_pos hM))
