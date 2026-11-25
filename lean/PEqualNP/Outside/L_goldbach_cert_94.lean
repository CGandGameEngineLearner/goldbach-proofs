import Mathlib

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_goldbach_cert_94 :
    ∀ a:ℕ, Nat.Coprime a 94 → (∑ b ∈ (Finset.range 94).filter (fun b => Nat.Coprime b 94), Complex.exp (((2*Real.pi*(a:ℝ)*b/94:ℝ):ℂ)*Complex.I))/(46:ℂ)=(1:ℂ)/46 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 94)
  let z := Complex.exp θ
  have hz : IsPrimitiveRoot z 94 := by
    simpa [z, θ] using Complex.isPrimitiveRoot_exp_of_coprime a 94 (by decide) ha
  have hsquare : IsPrimitiveRoot (z ^ 2) 47 :=
    IsPrimitiveRoot.pow (by decide : 0 < 94) hz (by decide)
  have hhalf : IsPrimitiveRoot (z ^ 47) 2 :=
    IsPrimitiveRoot.pow (by decide : 0 < 94) hz (by decide)
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 94 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    dsimp [θ]
    ring

  -- The odd residues are exactly the units together with 47.
  let units := (Finset.range 94).filter (fun b => Nat.Coprime b 94)
  let oddIndex : ℕ ↪ ℕ := ⟨fun j => 2 * j + 1, by intro i j hij; omega⟩
  have odds : insert 47 units = (Finset.range 47).map oddIndex := by
    dsimp only [units, oddIndex] <;> decide
  have missing : 47 ∉ units := by
    dsimp only [units] <;> decide

  -- The odd powers form a full geometric sum with ratio z² of order 47.
  have oddTotal : (∑ b ∈ insert 47 units, z ^ b) = 0 := by
    rw [odds, Finset.sum_map]
    change (∑ j ∈ Finset.range 47, z ^ (2 * j + 1)) = 0
    calc
      _ = ∑ j ∈ Finset.range 47, (z ^ 2) ^ j * z := by
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_succ, pow_mul]
      _ = 0 := by
        rw [← Finset.sum_mul, hsquare.geom_sum_eq_zero (by decide), zero_mul]
  rw [Finset.sum_insert missing, hhalf.eq_neg_one_of_two_right] at oddTotal
  have unitTotal : (∑ b ∈ units, z ^ b) = 1 := by
    linear_combination oddTotal
  simp_rw [phase]
  rw [unitTotal]
