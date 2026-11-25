import Mathlib

private theorem sum_units_94 (z : ℂ) (hz : IsPrimitiveRoot z 94) :
    (∑ b ∈ (Finset.range 94).filter (fun b => Nat.Coprime b 94), z ^ b) = 1 := by
  let odds := (Finset.range 47).image (fun j => 2 * j + 1)
  have hunits : (Finset.range 94).filter (fun b => Nat.Coprime b 94) = odds.erase 47 := by
    ext b
    simp only [odds, Finset.mem_erase, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    rw [show 94 = 2 * 47 by decide, Nat.coprime_mul_iff_right,
      (Nat.coprime_comm : b.Coprime 2 ↔ _), (Nat.coprime_comm : b.Coprime 47 ↔ _),
      Nat.prime_two.coprime_iff_not_dvd, (by decide : Nat.Prime 47).coprime_iff_not_dvd]
    constructor
    · rintro ⟨hb, h₂, h₄₇⟩
      exact ⟨by omega, b / 2, by omega, by omega⟩
    · rintro ⟨hne, j, hj, rfl⟩
      exact ⟨by omega, by omega, by omega⟩
  have hsquare : IsPrimitiveRoot (z ^ 2) 47 := IsPrimitiveRoot.pow (by decide) hz (by decide)
  have hhalf : IsPrimitiveRoot (z ^ 47) 2 := IsPrimitiveRoot.pow (by decide) hz (by decide)
  -- The sum over all odds is z times one complete geometric sum at z².
  have hsum : (∑ b ∈ odds, z ^ b) = 0 := by
    dsimp only [odds]
    rw [Finset.sum_image (fun i _ j _ hij => by omega)]
    simp_rw [pow_succ, pow_mul]
    rw [← Finset.sum_mul, hsquare.geom_sum_eq_zero (by decide), zero_mul]
  have hmem : 47 ∈ odds := Finset.mem_image.mpr ⟨23, by decide, rfl⟩
  have h := Finset.sum_erase_add odds (fun b => z ^ b) hmem
  rw [hsum, hhalf.eq_neg_one_of_two_right] at h
  rw [hunits]
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

theorem PEqualNP.Outside.L_goldbach_cert_94 :
    ∀ a:ℕ, Nat.Coprime a 94 → (∑ b ∈ (Finset.range 94).filter (fun b => Nat.Coprime b 94), Complex.exp (((2*Real.pi*(a:ℝ)*b/94:ℝ):ℂ)*Complex.I))/(46:ℂ)=(1:ℂ)/46 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 94)
  have hz : IsPrimitiveRoot (Complex.exp θ) 94 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 94 (by decide) ha
  apply congrArg (fun s : ℂ => s / 46)
  calc
    _ = ∑ b ∈ (Finset.range 94).filter (fun b => Nat.Coprime b 94), (Complex.exp θ) ^ b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp [θ]
      push_cast
      ring
    _ = 1 := sum_units_94 _ hz
