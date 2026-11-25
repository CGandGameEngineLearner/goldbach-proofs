import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_shift_window_budget :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let r := fun n : ℕ => (I n (high n) (high n)).re/(n:ℝ); ∀ n H : ℕ, ∀ e : ℝ, 0<n → 0<H → 0<e → (∑ j ∈ Finset.range H, (r (n+2*j))^2) < (H:ℝ)*e^2 → (∑ i ∈ Finset.range (H-1), max 0 (r (n+2*(i+1))-r (n+2*i))) ≤ e → -(2*e*(n:ℝ)) ≤ (I n (high n) (high n)).re := by
  intro w E S Q arcs low high I r n H e hn hH he energy variation
  have anchor : ∃ j < H, |r (n+2*j)| < e := by
    by_contra none
    push Not at none
    have lower : (H:ℝ)*e^2 ≤ ∑ j ∈ Finset.range H, (r (n+2*j))^2 := by
      calc
        _ = ∑ _j ∈ Finset.range H, e^2 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j hj => by
          have h := none j (Finset.mem_range.mp hj)
          nlinarith [sq_abs (r (n+2*j)), sq_nonneg (|r (n+2*j)|-e)])
    linarith
  obtain ⟨j,hj,small⟩ := anchor
  let diff (i : ℕ) := r (n+2*(i+1))-r (n+2*i)
  have tel : r (n+2*j)-r n = ∑ i ∈ Finset.range j, diff i := by
    simpa [diff] using (Finset.sum_range_sub (fun i => r (n+2*i)) j).symm
  have upper : r (n+2*j)-r n ≤ e := by
    rw [tel]
    refine (Finset.sum_le_sum (fun i _ => le_max_right 0 (diff i))).trans ?_
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : j ≤ H-1)) ?_).trans
    · exact variation
    · intro i _ _
      exact le_max_left 0 (diff i)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have lower : -(2*e) ≤ r n := by
    have := (abs_lt.mp small).1
    linarith
  have := mul_le_mul_of_nonneg_right lower hn'.le
  dsimp [r] at this
  have result : -(2*e*(n:ℝ)) ≤ (I n (high n) (high n)).re := by
    simpa [div_mul_cancel₀ _ hn'.ne', mul_assoc] using this
  exact result
