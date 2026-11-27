import Mathlib

theorem Conjectures.Goldbach.BulkEnergyToClipped :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ n:ℕ,2≤n → intervalIntegral (fun t => ‖S n (high n) t‖^2) (0:ℝ) 1 MeasureTheory.volume≤((n:ℝ)+1)*(Real.log (n:ℝ))^2) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2)); let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t)); ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152):= by
  intro h
  intro w2 E2 S2 Q2 arcs2 low2 high2 I2 L K J τ small n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hτ : 0 ≤ τ n := by
    dsimp only [τ]
    positivity
  have hsmall : ∀ t : ℝ, |small n t| ≤ τ n := by
    intro t
    dsimp only [small]
    have h1 : min (τ n) (1 - K n t) ≤ τ n := min_le_left _ _
    have h2 : -(τ n) ≤ τ n := by linarith
    exact abs_le.mpr ⟨le_max_left _ _, max_le h2 h1⟩
  have hS_cont : Continuous (fun t : ℝ => S2 n (high2 n) t) := by
    dsimp only [S2, E2]
    fun_prop
  have hSh_cont : Continuous (fun t : ℝ => ‖S2 n (high2 n) t‖ ^ 2) := (hS_cont.norm).pow 2
  have hSh_int : IntervalIntegrable (fun t : ℝ => τ n * ‖S2 n (high2 n) t‖ ^ 2)
      MeasureTheory.volume 0 1 := (continuous_const.mul hSh_cont).intervalIntegrable _ _
  have hpt : ∀ t : ℝ, ‖(arcs2 n)ᶜ.indicator
      (fun u => ((small n u : ℝ) : ℂ) * S2 n (high2 n) u * S2 n (high2 n) u * E2 (-(n : ℝ) * u)) t‖
      ≤ τ n * ‖S2 n (high2 n) t‖ ^ 2 := by
    intro t
    by_cases ht : t ∈ (arcs2 n)ᶜ
    · rw [Set.indicator_of_mem ht]
      have hnorm : ‖((small n t : ℝ) : ℂ) * S2 n (high2 n) t * S2 n (high2 n) t * E2 (-(n : ℝ) * t)‖
          = |small n t| * ‖S2 n (high2 n) t‖ ^ 2 := by
        simp only [norm_mul, E2, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
        ring
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right (hsmall t) (sq_nonneg _)
    · rw [Set.indicator_of_notMem ht, norm_zero]
      exact mul_nonneg hτ (sq_nonneg _)
  have hJ : |J n (small n)| ≤ ‖intervalIntegral
      (fun t => (arcs2 n)ᶜ.indicator
        (fun u => ((small n u : ℝ) : ℂ) * S2 n (high2 n) u * S2 n (high2 n) u * E2 (-(n : ℝ) * u)) t)
      (0 : ℝ) 1 MeasureTheory.volume‖ := by
    dsimp only [J]
    exact Complex.abs_re_le_norm _
  have hbound : ‖intervalIntegral
      (fun t => (arcs2 n)ᶜ.indicator
        (fun u => ((small n u : ℝ) : ℂ) * S2 n (high2 n) u * S2 n (high2 n) u * E2 (-(n : ℝ) * u)) t)
      (0 : ℝ) 1 MeasureTheory.volume‖
      ≤ intervalIntegral (fun t => τ n * ‖S2 n (high2 n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · exact Filter.Eventually.of_forall (fun t _ => hpt t)
    · exact hSh_int
  have henergy : intervalIntegral (fun t => ‖S2 n (high2 n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume
      ≤ ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 := h n hn
  have hsplit : intervalIntegral (fun t => τ n * ‖S2 n (high2 n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume
      = τ n * intervalIntegral (fun t => ‖S2 n (high2 n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume :=
    intervalIntegral.integral_const_mul _ _
  have hmain : |J n (small n)| ≤ τ n * (((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
    calc |J n (small n)| ≤ _ := hJ
      _ ≤ _ := hbound
      _ = τ n * intervalIntegral (fun t => ‖S2 n (high2 n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume := hsplit
      _ ≤ τ n * (((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hτ
  refine hmain.trans ?_
  have hden : (0 : ℝ) < 2304 * (1 + (Real.log (n : ℝ)) ^ 2) := by positivity
  have hA : ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 ≤ 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hB : 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ 2 * (n : ℝ) * (1 + (Real.log (n : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith [sq_nonneg (Real.log (n : ℝ))]) (by positivity)
  have hτeq : τ n * (((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2)
      = ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 / (2304 * (1 + (Real.log (n : ℝ)) ^ 2)) := by
    dsimp only [τ]
    ring
  rw [hτeq, div_le_iff₀ hden]
  have hrw : (n : ℝ) / 1152 * (2304 * (1 + (Real.log (n : ℝ)) ^ 2))
      = 2 * (n : ℝ) * (1 + (Real.log (n : ℝ)) ^ 2) := by ring
  rw [hrw]
  exact hA.trans hB
