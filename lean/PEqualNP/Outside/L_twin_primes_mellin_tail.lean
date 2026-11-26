import Mathlib

namespace PEqualNP.Outside

private lemma step_geom5 (t : ℝ) (ht : 1 ≤ t) :
    (1:ℝ)/(t+1)^5 ≤ (1/4)*((1/t^4) - (1/(t+1)^4)) := by
  have ht0 : (0:ℝ) < t := by linarith
  have ht1 : (0:ℝ) < t + 1 := by linarith
  have hfac : (t+1)^4 - t^4 = 4*t^3 + 6*t^2 + 4*t + 1 := by ring
  have key : 4 * t^4 ≤ (t+1) * ((t+1)^4 - t^4) := by
    rw [hfac]
    nlinarith [ht0, ht]
  have key2 : 4 * (t^4 * (t+1)^4) ≤ ((t+1)^4 - t^4) * (t+1)^5 := by
    have hmul := mul_le_mul_of_nonneg_right key (le_of_lt (by positivity : (0:ℝ) < (t+1)^4))
    calc 4 * (t^4 * (t+1)^4) = (4 * t^4) * (t+1)^4 := by ring
      _ ≤ ((t+1) * ((t+1)^4 - t^4)) * (t+1)^4 := hmul
      _ = ((t+1)^4 - t^4) * (t+1)^5 := by ring
  have hA : (1:ℝ)/t^4 - 1/(t+1)^4 = ((t+1)^4 - t^4)/(t^4 * (t+1)^4) := by
    field_simp
  have hB : (1:ℝ)/4 * (((t+1)^4 - t^4)/(t^4 * (t+1)^4))
      = ((t+1)^4 - t^4)/(4 * (t^4 * (t+1)^4)) := by
    field_simp
  rw [hA, hB]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (t+1)^5)
      (by positivity : (0:ℝ) < 4 * (t^4 * (t+1)^4))]
  simpa using key2

private lemma tail5 (y : ℝ) (hy : 1 ≤ y) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1:ℝ)/(y+(n:ℝ))^5 ≤ (5/4)*(1/y^4) := by
  have hypos : (0:ℝ) < y := by linarith
  cases N with
  | zero =>
    rw [Finset.sum_range_zero]
    have h1 : (0:ℝ) < 1/y^4 := by positivity
    nlinarith
  | succ M =>
    rw [Finset.sum_range_succ']
    have hzero : (1:ℝ)/(y+((0:ℕ):ℝ))^5 ≤ (1:ℝ)/y^4 := by
      simp only [Nat.cast_zero, add_zero]
      rw [div_le_div_iff₀ (pow_pos hypos 5) (pow_pos hypos 4)]
      have hfac2 : y^5 - y^4 = y^4 * (y - 1) := by ring
      nlinarith [hfac2, pow_pos hypos 4, hy]
    have hpt : ∀ i : ℕ,
        (1:ℝ)/(y+((i+1:ℕ):ℝ))^5
          ≤ (1/4)*((1/(y+(i:ℝ))^4) - (1/(y+((i+1:ℕ):ℝ))^4)) := by
      intro i
      have ht : (1:ℝ) ≤ y + (i:ℝ) := by
        have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
        linarith
      have h := step_geom5 (y + (i:ℝ)) ht
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h
    have hrest : ∑ i ∈ Finset.range M, (1:ℝ)/(y+((i+1:ℕ):ℝ))^5 ≤ (1/4)*(1/y^4) := by
      calc ∑ i ∈ Finset.range M, (1:ℝ)/(y+((i+1:ℕ):ℝ))^5
          ≤ ∑ i ∈ Finset.range M, (1/4)*((1/(y+(i:ℝ))^4) - (1/(y+((i+1:ℕ):ℝ))^4)) :=
            Finset.sum_le_sum (fun i _ => hpt i)
        _ = (1/4) * ∑ i ∈ Finset.range M, ((1/(y+(i:ℝ))^4) - (1/(y+((i+1:ℕ):ℝ))^4)) := by
            rw [Finset.mul_sum]
        _ = (1/4) * ((1/y^4) - (1/(y+(M:ℝ))^4)) := by
            rw [Finset.sum_range_sub']
            simp
        _ ≤ (1/4) * (1/y^4) := by
            have hnn : (0:ℝ) ≤ 1/(y+(M:ℝ))^4 := by positivity
            nlinarith
    simp only [Nat.cast_zero, add_zero] at hzero ⊢
    linarith [hzero, hrest]

theorem L_twin_primes_mellin_tail :
    ∀ C : ℝ, 0 ≤ C → ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℕ) (m : ℕ → ℝ),
      (∀ n, 0 ≤ m n ∧ m n ≤ C*Real.log (2+(n:ℝ))) →
      (∑' n : ℕ, m (L+n)/(1+(L:ℝ)+n)^6) ≤ D/(1+(L:ℝ))^4 := by
  intro C hC
  refine ⟨4*C, by linarith, ?_⟩
  intro L m hm
  set y : ℝ := 1 + (L:ℝ) with hy
  have hy1 : (1:ℝ) ≤ y := by
    rw [hy]
    have hL : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
    linarith
  have hypos : (0:ℝ) < y := by linarith
  have hpt : ∀ n : ℕ, m (L+n)/(y+(n:ℝ))^6 ≤ C/(y+(n:ℝ))^5 := by
    intro n
    have hn := hm (L+n)
    have hyn : (0:ℝ) < y + (n:ℝ) := by
      have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hlog : Real.log (2+((L+n:ℕ):ℝ)) ≤ y + (n:ℝ) := by
      have hpos : (0:ℝ) < 2+((L+n:ℕ):ℝ) := by positivity
      have h1 := Real.log_le_sub_one_of_pos hpos
      have harith : 2+((L+n:ℕ):ℝ) - 1 = y + (n:ℝ) := by
        rw [hy]
        push_cast
        ring
      linarith
    have hmul : m (L+n) ≤ C*(y+(n:ℝ)) := by
      calc m (L+n) ≤ C*Real.log (2+((L+n:ℕ):ℝ)) := hn.2
        _ ≤ C*(y+(n:ℝ)) := mul_le_mul_of_nonneg_left hlog hC
    have hd : m (L+n)*(y+(n:ℝ))^5 ≤ (C*(y+(n:ℝ)))*(y+(n:ℝ))^5 :=
      mul_le_mul_of_nonneg_right hmul (le_of_lt (pow_pos hyn 5))
    rw [div_le_div_iff₀ (pow_pos hyn 6) (pow_pos hyn 5)]
    calc m (L+n) * (y+(n:ℝ))^5
        ≤ (C*(y+(n:ℝ))) * (y+(n:ℝ))^5 := hd
      _ = C * (y+(n:ℝ))^6 := by ring
  have hbnd : ∀ N : ℕ, ∑ n ∈ Finset.range N, m (L+n)/(y+(n:ℝ))^6 ≤ (4*C)*(1/y^4) := by
    intro N
    calc ∑ n ∈ Finset.range N, m (L+n)/(y+(n:ℝ))^6
        ≤ ∑ n ∈ Finset.range N, C/(y+(n:ℝ))^5 :=
          Finset.sum_le_sum (fun n _ => hpt n)
      _ = C * (∑ n ∈ Finset.range N, (1/(y+(n:ℝ))^5)) := by
          simp only [div_eq_mul_inv, one_mul]
          rw [Finset.mul_sum]
      _ ≤ C * ((5/4)*(1/y^4)) := mul_le_mul_of_nonneg_left (tail5 y hy1 N) hC
      _ ≤ (4*C)*(1/y^4) := by
          have hy4 : (0:ℝ) < 1/y^4 := by positivity
          nlinarith [hC, hy4]
  have hf : ∀ n : ℕ, 0 ≤ m (L+n)/(y+(n:ℝ))^6 := by
    intro n
    have hn := hm (L+n)
    have hden : (0:ℝ) < (y+(n:ℝ))^6 :=
      pow_pos (by
        have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith : (0:ℝ) < y + (n:ℝ)) 6
    exact div_nonneg hn.1 (le_of_lt hden)
  have hmain : (∑' n : ℕ, m (L+n)/(y+(n:ℝ))^6) ≤ (4*C)*(1/y^4) :=
    Real.tsum_le_of_sum_range_le hf hbnd
  have hyeq : y = 1 + (L:ℝ) := hy
  rw [hyeq] at hmain ⊢
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmain

end PEqualNP.Outside

