import Mathlib

theorem Conjectures.JoshiAbc.LegendreThreshold :
    ∀ l Q : ℝ, 7 ≤ l → (l*(l+1)/12-1)*Q ≤ (l+5)/4*Real.log Real.pi → 2*l*Q ≤ 126/11*Real.log Real.pi := by
  intro l Q hl h
  have hL : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have h1 : (l*l + l - 12)*Q ≤ 3*(l+5)*Real.log Real.pi := by linarith
  have h22 : (0:ℝ) ≤ 22*l := by nlinarith
  have h2 : (22*l)*((l*l + l - 12)*Q) ≤ (22*l)*(3*(l+5)*Real.log Real.pi) :=
    mul_le_mul_of_nonneg_left h1 h22
  have hfac : 0 ≤ (l-7)*(5*l+18) := mul_nonneg (by linarith) (by linarith)
  have h3 : 66*l*(l+5) ≤ 126*(l*l + l - 12) := by nlinarith [hfac]
  have h4 : (66*l*(l+5))*Real.log Real.pi ≤ (126*(l*l + l - 12))*Real.log Real.pi :=
    mul_le_mul_of_nonneg_right h3 hL.le
  have e1 : (22*l)*((l*l + l - 12)*Q) = (l*l + l - 12)*(22*l*Q) := by ring
  have e2 : (22*l)*(3*(l+5)*Real.log Real.pi) = (66*l*(l+5))*Real.log Real.pi := by ring
  have e3 : (126*(l*l + l - 12))*Real.log Real.pi = (l*l + l - 12)*(126*Real.log Real.pi) := by ring
  have h5 : (l*l + l - 12)*(22*l*Q) ≤ (l*l + l - 12)*(126*Real.log Real.pi) := by
    rw [← e1, ← e3]
    exact h2.trans (by rw [e2]; exact h4)
  have hpos : 0 < l*l + l - 12 := by
    have hp : 0 < (l-3)*(l+4) := mul_pos (by linarith) (by linarith)
    nlinarith [hp]
  have h6 : 22*l*Q ≤ 126*Real.log Real.pi := le_of_mul_le_mul_left h5 hpos
  linarith
