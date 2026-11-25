import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_shift_window_budget :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let r := fun n : ℕ => (I n (high n) (high n)).re/(n:ℝ); ∀ n H : ℕ, ∀ e : ℝ, 0<n → 0<H → 0<e → (∑ j ∈ Finset.range H, (r (n+2*j))^2) < (H:ℝ)*e^2 → (∑ i ∈ Finset.range (H-1), max 0 (r (n+2*(i+1))-r (n+2*i))) ≤ e → -(2*e*(n:ℝ)) ≤ (I n (high n) (high n)).re := by
  intro w E S Q arcs low high I r n H e hn hH he h1 h2
  have hdef : ∀ m : ℕ, r m = (I m (high m) (high m)).re / (m:ℝ) := fun _ => rfl
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hnR0 : (n:ℝ) ≠ 0 := by
    have hnz : n ≠ 0 := by omega
    exact_mod_cast hnz
  have hex : ∃ j ∈ Finset.range H, (r (n+2*j))^2 < e^2 := by
    by_contra hcon
    push_neg at hcon
    have hsum : (Finset.range H).sum (fun _ : ℕ => e^2) ≤ (Finset.range H).sum (fun j => (r (n+2*j))^2) :=
      Finset.sum_le_sum (fun j hj => hcon j hj)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul'] at hsum
    have hcomm : e ^ 2 * (H:ℝ) = (H:ℝ) * e ^ 2 := mul_comm _ _
    linarith
  obtain ⟨j, hj, hsq⟩ := hex
  obtain ⟨hlo, _⟩ := abs_lt_of_sq_lt_sq' hsq (le_of_lt he)
  have hcore : (-2:ℝ)*e ≤ r n := by
    rcases Nat.lt_or_ge j 1 with h0 | hpos
    · have hz : n + 2*j = n := by omega
      rw [hz] at hlo
      linarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hpos
      have hz0 : n + 2*0 = n := by omega
      have hsub : r (n + 2*(i+1)) - r n ≤ e := by
        have gen : ∀ m : ℕ, ∑ k ∈ Finset.range m, (r (n + 2*(k+1)) - r (n + 2*k)) = r (n + 2*m) - r (n + 2*0) := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            have hs : ∑ k ∈ Finset.range (m+1), (r (n + 2*(k+1)) - r (n + 2*k)) = (∑ k ∈ Finset.range m, (r (n + 2*(k+1)) - r (n + 2*k))) + (r (n + 2*(m+1)) - r (n + 2*m)) := Finset.sum_range_succ _ _
            rw [hs, ih]
            ring
        have htele : r (n + 2*(i+1)) - r n = ∑ k ∈ Finset.range (i+1), (r (n + 2*(k+1)) - r (n + 2*k)) := by
          rw [gen (i+1), hz0]
        have hstep : ∑ k ∈ Finset.range (i+1), (r (n + 2*(k+1)) - r (n + 2*k)) ≤ ∑ k ∈ Finset.range (i+1), max 0 (r (n + 2*(k+1)) - r (n + 2*k)) :=
          Finset.sum_le_sum (fun k _ => le_max_right _ _)
        have hjlt : i + 1 ≤ H - 1 := by
          have hji : 1 + i < H := Finset.mem_range.mp hj
          omega
        have hmono : ∑ k ∈ Finset.range (i+1), max 0 (r (n + 2*(k+1)) - r (n + 2*k)) ≤ ∑ k ∈ Finset.range (H-1), max 0 (r (n + 2*(k+1)) - r (n + 2*k)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hjlt)
          intro k _ _
          exact le_max_left 0 _
        rw [htele]
        linarith
      have hlo' : -e < r (n + 2*(i+1)) := by
        have hidx : n + 2*(1+i) = n + 2*(i+1) := by omega
        rw [hidx] at hlo
        exact hlo
      linarith
  have hIr : (I n (high n) (high n)).re = r n * (n:ℝ) := by
    rw [hdef n]
    field_simp [hnR0]
  rw [hIr, show -(2*e*(n:ℝ)) = (-2:ℝ)*e*(n:ℝ) from by ring]
  exact mul_le_mul_of_nonneg_right hcore hnR.le
