import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_minor_shift_window_budget :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let r := fun n : ℕ => (I n (high n) (high n)).re/(n:ℝ); ∀ n H : ℕ, ∀ e : ℝ, 0<n → 0<H → 0<e → (∑ j ∈ Finset.range H, (r (n+2*j))^2) < (H:ℝ)*e^2 → (∑ i ∈ Finset.range (H-1), max 0 (r (n+2*(i+1))-r (n+2*i))) ≤ e → -(2*e*(n:ℝ)) ≤ (I n (high n) (high n)).re := by
  classical
  intro w E S Q arcs low high I r n H e hn _hH he henergy hvariation
  have floor_bound (a : ℕ → ℝ) (m : ℕ) (b : ℝ) (hb : 0 < b)
      (energy : (∑ j ∈ Finset.range m, (a j)^2) < (m:ℝ)*b^2)
      (variation : (∑ i ∈ Finset.range (m-1), max 0 (a (i+1)-a i)) ≤ b) :
      -(2*b) ≤ a 0 := by
    have anchor : ∃ j ∈ Finset.range m, -b ≤ a j := by
      by_contra hnone
      have every (j : ℕ) (hj : j ∈ Finset.range m) : b^2 ≤ (a j)^2 := by
        have hlt : a j < -b := lt_of_not_ge (fun h => hnone ⟨j, hj, h⟩)
        have hsq := mul_self_le_mul_self hb.le (show b ≤ -a j by linarith)
        nlinarith only [hsq]
      have hsum := Finset.sum_le_sum every
      have hlarge : (m:ℝ)*b^2 ≤ ∑ j ∈ Finset.range m, (a j)^2 := by
        simpa using hsum
      exact (not_lt_of_ge hlarge) energy
    obtain ⟨j, hj, ha⟩ := anchor
    have telescope (l : ℕ) :
        a l - a 0 ≤ ∑ i ∈ Finset.range l, max 0 (a (i+1)-a i) := by
      induction l with
      | zero => simp
      | succ i ih =>
        rw [Finset.sum_range_succ]
        linarith [le_max_right (0:ℝ) (a (i+1)-a i)]
    have hj' := Finset.mem_range.mp hj
    have hpartial : (∑ i ∈ Finset.range j, max 0 (a (i+1)-a i)) ≤
        ∑ i ∈ Finset.range (m-1), max 0 (a (i+1)-a i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ => le_max_left _ _)
    linarith [telescope j]
  have h := floor_bound (fun j => r (n+2*j)) H e he henergy hvariation
  have hnorm : -(2*e) ≤ (I n (high n) (high n)).re/(n:ℝ) := by
    simpa only [Nat.mul_zero, Nat.add_zero] using h
  have hden : (0:ℝ) < n := by exact_mod_cast hn
  simpa only [neg_mul] using (le_div_iff₀ hden).mp hnorm
