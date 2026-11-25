import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_shift_window_budget :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let r := fun n : ℕ => (I n (high n) (high n)).re/(n:ℝ); ∀ n H : ℕ, ∀ e : ℝ, 0<n → 0<H → 0<e → (∑ j ∈ Finset.range H, (r (n+2*j))^2) < (H:ℝ)*e^2 → (∑ i ∈ Finset.range (H-1), max 0 (r (n+2*(i+1))-r (n+2*i))) ≤ e → -(2*e*(n:ℝ)) ≤ (I n (high n) (high n)).re := by
  intro w E S Q arcs low high I r n H e hn _hH he henergy hvariation
  let u (j : ℕ) := r (n + 2*j)
  let variation (i : ℕ) := max 0 (u (i+1) - u i)
  have hanchor : ∃ j ∈ Finset.range H, -e < u j := by
    by_contra! h
    have hsum : (∑ _j ∈ Finset.range H, e^2) ≤ ∑ j ∈ Finset.range H, (u j)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := h j hj
      nlinarith [mul_nonneg (show 0 ≤ -u j-e by linarith) (show 0 ≤ -u j+e by linarith)]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    exact (not_lt_of_ge hsum) henergy
  obtain ⟨j, hj, hnear⟩ := hanchor
  have htel (t : ℕ) : u t - u 0 ≤ ∑ i ∈ Finset.range t, variation i := by
    induction t with
    | zero => simp
    | succ t ih =>
        rw [Finset.sum_range_succ]
        have hstep : u (t+1) - u t ≤ variation t := le_max_right _ _
        linarith
  have hpref : (∑ i ∈ Finset.range j, variation i) ≤ ∑ i ∈ Finset.range (H-1), variation i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.range_mono
      have := Finset.mem_range.mp hj
      omega
    · exact fun i _ _ => le_max_left _ _
  have hv : (∑ i ∈ Finset.range (H-1), variation i) ≤ e := hvariation
  have hu : -(2*e) ≤ u 0 := by linarith [htel j]
  have hr : -(2*e) ≤ (I n (high n) (high n)).re / (n:ℝ) := by simpa [u, r] using hu
  simpa only [neg_mul] using (le_div_iff₀ (show (0:ℝ) < n by exact_mod_cast hn)).mp hr
