import Mathlib

theorem Conjectures.Cuts.Task6fbf6c968d8563e59fed9ba9 : (by
  classical
  exact ∀ (U : Finset ℕ) (r : ℕ → ℕ) (M : ℕ), (∀ n ∈ U, r n ≤ M) →
    (((U.filter (fun n => r n=1)).card):ℤ) = ∑ j ∈ Finset.range M, (-1:ℤ)^j * ((j+1:ℕ):ℤ) * ((∑ n ∈ U, (r n).choose (j+1) : ℕ):ℤ)) := by
  classical
  intro U r M hM
  have invert (x : ℕ) (hx : x ≤ M) :
      (∑ j ∈ Finset.range M, (-1:ℤ)^j * ((j+1:ℕ):ℤ) * (x.choose (j+1):ℤ)) = if x=1 then 1 else 0 := by
    cases x with
    | zero => simp
    | succ m =>
      have coeff (j : ℕ) : (-1:ℤ)^j * ((j+1:ℕ):ℤ) * ((m+1).choose (j+1):ℤ) =
          ((m+1:ℕ):ℤ) * ((-1:ℤ)^j * (m.choose j:ℤ)) := by
        have hh := congrArg (fun n : ℕ => (n:ℤ)) (Nat.add_one_mul_choose_eq m j)
        push_cast at hh ⊢
        linear_combination -((-1:ℤ)^j)*hh
      simp_rw [coeff]
      rw [← Finset.mul_sum]
      have pad : (∑ j ∈ Finset.range (m+1), (-1:ℤ)^j * (m.choose j:ℤ)) =
          ∑ j ∈ Finset.range M, (-1:ℤ)^j * (m.choose j:ℤ) := by
        apply Finset.sum_subset (Finset.range_mono hx)
        intro j _ hj
        have hlt : m < j := by simpa using hj
        simp [Nat.choose_eq_zero_of_lt hlt]
      rw [← pad, Int.alternating_sum_range_choose]
      by_cases hm : m=0 <;> simp [hm]
  calc
    _ = ∑ n ∈ U, if r n=1 then (1:ℤ) else 0 := (Finset.sum_boole _ _).symm
    _ = ∑ n ∈ U, ∑ j ∈ Finset.range M, (-1:ℤ)^j * ((j+1:ℕ):ℤ) * ((r n).choose (j+1):ℤ) :=
      Finset.sum_congr rfl (fun n hn => (invert (r n) (hM n hn)).symm)
    _ = _ := by rw [Finset.sum_comm]; push_cast; simp only [Finset.mul_sum]
