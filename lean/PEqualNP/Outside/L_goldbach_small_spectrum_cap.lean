import Mathlib

theorem PEqualNP.Outside.L_goldbach_small_spectrum_cap :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
    let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
    let high := fun (n k : ℕ) => w k-low n k;
    let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
    ∀ (n:ℕ) (t:ℝ), 2≤n → ‖S n (low n) t‖≤((n:ℝ)^(1/3:ℝ)+1)*Real.log (n:ℝ) := by
  intro w E S Q arcs low high I n t hn
  classical
  let support := (Finset.range (n + 1)).filter (fun k => k ^ 3 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hphase (x : ℝ) : ‖E x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      ‖(low n k : ℂ) * E ((k : ℝ) * t)‖ ≤
        if k ^ 3 ≤ n then Real.log (n : ℝ) else 0 := by
    rw [norm_mul, hphase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    by_cases hcube : k ^ 3 ≤ n
    · by_cases hp : Nat.Prime k
      · have hkpos : 0 < (k : ℝ) := by exact_mod_cast hp.pos
        have hkone : 1 ≤ (k : ℝ) := by exact_mod_cast hp.one_le
        have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simpa only [low, w, ite_eq_left hcube, ite_eq_left hp,
          abs_of_nonneg (Real.log_nonneg hkone)] using
          (Real.log_le_log hkpos (by exact_mod_cast hkn) : Real.log (k : ℝ) ≤ Real.log (n : ℝ))
      · simpa [low, w, hcube, hp] using hlog
    · simp [low, hcube]
  have hcard : support.card ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ + 1 := by
    have hsub : support ⊆ Finset.range (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ + 1) := by
      intro k hk
      have hcube : k ^ 3 ≤ n := (Finset.mem_filter.mp hk).2
      have hreal : (k : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hcube
      have hroot : (k : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
        calc
          (k : ℝ) = ((k : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
            simpa only [one_div, Nat.cast_ofNat] using
              (Real.pow_rpow_inv_natCast (x := (k : ℝ)) (n := 3) (by positivity) (by decide)).symm
          _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hreal (by norm_num)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hroot))
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hcount : (support.card : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) + 1 := by
    calc
      (support.card : ℝ) ≤ (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
      _ ≤ _ := add_le_add (Nat.floor_le (a := (n : ℝ) ^ (1 / 3 : ℝ)) (by positivity)) (le_refl 1)
  calc
    ‖S n (low n) t‖ ≤ ∑ k ∈ Finset.range (n + 1), ‖(low n k : ℂ) * E ((k : ℝ) * t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (if k ^ 3 ≤ n then Real.log (n : ℝ) else 0) :=
      Finset.sum_le_sum hterm
    _ = ∑ _k ∈ support, Real.log (n : ℝ) := by simp only [support, Finset.sum_filter]
    _ = (support.card : ℝ) * Real.log (n : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hlog
