import Mathlib

namespace CubicWindow

private def moment (a : Fin 3 → ℤ) (j : ℕ) := ∑ i, a i ^ j

private lemma perm_of_moments (a b : Fin 3 → ℤ)
    (h₁ : moment a 1 = moment b 1) (h₂ : moment a 2 = moment b 2)
    (h₃ : moment a 3 = moment b 3) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i, a i = b (σ i) := by
  simp only [moment, Fin.sum_univ_three, pow_one] at h₁ h₂ h₃
  let s := a 0 + a 1 + a 2
  let t := b 0 + b 1 + b 2
  let q := a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2
  have pairEq : 2*(a 0*a 1 + a 0*a 2 + a 1*a 2 - (b 0*b 1 + b 0*b 2 + b 1*b 2)) = 0 := by
    linear_combination (s+t)*h₁ - h₂
  have tripleEq : 6*(a 0*a 1*a 2 - b 0*b 1*b 2) = 0 := by
    linear_combination (s^2+s*t+t^2-3*q)*h₁ - 3*t*h₂ + 2*h₃
  have root : (a 0 - b 0)*(a 0 - b 1)*(a 0 - b 2) = 0 := by
    have : 6*((a 0 - b 0)*(a 0 - b 1)*(a 0 - b 2)) = 0 := by
      linear_combination 6*(a 0)^2*h₁ - 3*a 0*pairEq + tripleEq
    omega
  have lastTwo (u v r w : ℤ) (h : u+v=r+w) (h' : u^2+v^2=r^2+w^2) :
      (u = r ∧ v = w) ∨ (u = w ∧ v = r) := by
    have hz : 2*((u-r)*(u-w)) = 0 := by
      linear_combination (u-v-r-w)*h + h'
    have : (u-r)*(u-w) = 0 := by omega
    rcases mul_eq_zero.mp this with e|e <;> omega
  have makePerm (j k l : Fin 3) (h : Function.Bijective ![j,k,l])
      (e : a 0 = b j) (f : a 1 = b k) (g : a 2 = b l) :
      ∃ σ : Equiv.Perm (Fin 3), ∀ i, a i = b (σ i) := by
    refine ⟨Equiv.ofBijective ![j,k,l] h, ?_⟩
    intro i
    fin_cases i <;> assumption
  rcases mul_eq_zero.mp root with h|h
  · rcases mul_eq_zero.mp h with z|z
    · have h0 := sub_eq_zero.mp z
      rcases lastTwo (a 1) (a 2) (b 1) (b 2) (by omega) (by rw [h0] at h₂; omega) with ⟨e,f⟩|⟨e,f⟩
      · exact makePerm 0 1 2 (by decide) h0 e f
      · exact makePerm 0 2 1 (by decide) h0 e f
    · have h0 := sub_eq_zero.mp z
      rcases lastTwo (a 1) (a 2) (b 0) (b 2) (by omega) (by rw [h0] at h₂; omega) with ⟨e,f⟩|⟨e,f⟩
      · exact makePerm 1 0 2 (by decide) h0 e f
      · exact makePerm 1 2 0 (by decide) h0 e f
  · have h0 := sub_eq_zero.mp h
    rcases lastTwo (a 1) (a 2) (b 0) (b 1) (by omega) (by rw [h0] at h₂; omega) with ⟨e,f⟩|⟨e,f⟩
    · exact makePerm 2 0 1 (by decide) h0 e f
    · exact makePerm 2 1 0 (by decide) h0 e f

private lemma small_digit {X d v : ℤ} (bound : |d| < X) (heq : X*v + d = 0) : d = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (show X ∣ d from ⟨-v, by linarith⟩)
  have hx : 0 ≤ X := le_trans (abs_nonneg d) bound.le
  have : (d.natAbs : ℤ) < (X.natAbs : ℤ) := by simpa only [Int.natCast_natAbs, abs_of_nonneg hx] using bound
  exact_mod_cast this

private lemma moment_le (u : Fin 3 → ℤ) (H : ℕ) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ H)
    (j : ℕ) (hj : j ≤ 3) : 0 ≤ moment u j ∧ moment u j ≤ 3*((H:ℤ)+1)^3 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => pow_nonneg (hu i).1 j
  calc
    moment u j ≤ ∑ _i : Fin 3, ((H:ℤ)+1)^3 := by
      apply Finset.sum_le_sum
      intro i _
      exact (pow_le_pow_left₀ (hu i).1 (by linarith [(hu i).2] : u i ≤ (H:ℤ)+1) j).trans
        (pow_le_pow_right₀ (by omega : 1 ≤ (H:ℤ)+1) hj)
    _ = _ := by simp

end CubicWindow

open CubicWindow in
theorem Conjectures.Goldbach.CubicShortIntervalRigidity :
by
  classical
  exact ∀ P : Polynomial ℤ, P.natDegree=3 → ∃ C : ℕ, 0<C ∧ ∀ X H : ℕ, 1≤H → C*(H+1)^3 ≤ X → ∀ a b : Fin 3 → ℕ, (∀ i, a i ∈ Finset.Icc X (X+H) ∧ b i ∈ Finset.Icc X (X+H)) → (∑ i, P.eval ((a i):ℤ)) = (∑ i, P.eval ((b i):ℤ)) → ∃ σ : Equiv.Perm (Fin 3), ∀ i, a i=b (σ i) := by
  classical
  intro P hP
  let c := P.coeff
  have h3 : c 3 ≠ 0 := by
    change P.coeff 3 ≠ 0
    rw [← hP]
    exact Polynomial.coeff_natDegree (p := P) ▸ Polynomial.leadingCoeff_ne_zero.mpr (by intro h; simp [h] at hP)
  let C := 12 * ((c 1).natAbs + (c 2).natAbs + (c 3).natAbs + 1)
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro X H _hH hX a b hab heval
  let u (i : Fin 3) : ℤ := (a i : ℤ) - X
  let v (i : Fin 3) : ℤ := (b i : ℤ) - X
  have uv (i : Fin 3) : (0 ≤ u i ∧ u i ≤ H) ∧ (0 ≤ v i ∧ v i ≤ H) := by
    have h := hab i
    simp only [Finset.mem_Icc] at h
    dsimp [u,v]; omega
  let d (j : ℕ) := moment u j - moment v j
  let B : ℤ := ((H:ℤ)+1)^3
  have hd (j : ℕ) (hj : j ≤ 3) : |d j| ≤ 3*B := by
    have e := moment_le u H (fun i => (uv i).1) j hj
    have f := moment_le v H (fun i => (uv i).2) j hj
    exact abs_le.mpr (by dsimp [d,B]; omega)
  have hscale : 12*(|c 1|+|c 2|+|c 3|+1)*B ≤ (X:ℤ) := by
    have hx' : (C:ℤ)*((H:ℤ)+1)^3 ≤ (X:ℤ) := by exact_mod_cast hX
    simpa [C,B, Int.natCast_natAbs] using hx'
  have hB : 0 < B := by dsimp [B]; positivity
  have eval (y : ℤ) : P.eval y = c 0 + c 1*y + c 2*y^2 + c 3*y^3 := by
    rw [Polynomial.eval_eq_sum_range, hP]
    simp [Finset.sum_range_succ, c]
  have equation : (X:ℤ)*((X:ℤ)*(3*c 3*d 1) + (3*c 3*d 2+2*c 2*d 1))
        + (c 3*d 3+c 2*d 2+c 1*d 1) = 0 := by
    simp only [Fin.sum_univ_three, eval] at heval
    dsimp [d,moment,u,v]
    simp only [Fin.sum_univ_three]
    linear_combination heval
  have term (k j : ℕ) (hj : j ≤ 3) : |c k*d j| ≤ |c k| * (3*B) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hd j hj) (abs_nonneg _)
  have pos (i : ℕ) : 0 ≤ |c i| * B := mul_nonneg (abs_nonneg _) hB.le
  have low : c 3*d 3+c 2*d 2+c 1*d 1 = 0 := by
    apply small_digit (v := (X:ℤ)*(3*c 3*d 1) + (3*c 3*d 2+2*c 2*d 1)) _ equation
    calc
      _ ≤ (|c 3*d 3|+|c 2*d 2|)+|c 1*d 1| := (abs_add_le ..).trans (add_le_add (abs_add_le ..) (le_refl _))
      _ < _ := by linarith only [term 3 3 (by decide), term 2 2 (by decide), term 1 1 (by decide), pos 1,pos 2,pos 3,hB,hscale]
  have hXpos : (X:ℤ) ≠ 0 := by linarith only [pos 1,pos 2,pos 3,hscale,hB]
  rw [low,add_zero] at equation
  have rest := (mul_eq_zero.mp equation).resolve_left hXpos
  have mid : 3*c 3*d 2+2*c 2*d 1 = 0 := by
    apply small_digit (v := 3*c 3*d 1) _ rest
    calc
      _ ≤ |3*(c 3*d 2)|+|2*(c 2*d 1)| := by simpa only [mul_assoc] using (abs_add_le (3*c 3*d 2) (2*c 2*d 1))
      _ < _ := by
        rw [abs_mul (3:ℤ), abs_mul (2:ℤ), show |(3:ℤ)| = 3 by decide, show |(2:ℤ)| = 2 by decide]

        linarith only [term 3 2 (by decide), term 2 1 (by decide), pos 1,pos 2,pos 3,hB,hscale]
  rw [mid,add_zero] at rest
  have d1 : d 1 = 0 := by rcases mul_eq_zero.mp rest with e|e; contradiction; simpa [h3] using e
  have d2 : d 2 = 0 := by simpa [d1,h3] using mid
  have d3 : d 3 = 0 := by simpa [d1,d2,h3] using low
  obtain ⟨σ,hσ⟩ := perm_of_moments u v (sub_eq_zero.mp d1) (sub_eq_zero.mp d2) (sub_eq_zero.mp d3)
  refine ⟨σ,fun i => ?_⟩
  have e := hσ i
  dsimp [u,v] at e
  omega
