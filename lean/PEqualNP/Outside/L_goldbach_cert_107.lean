import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_cert_107 :
    ∀ a:ℕ, Nat.Coprime a 107 → (∑ b ∈ (Finset.range 107).filter (fun b => Nat.Coprime b 107), Complex.exp (((2*Real.pi*(a:ℝ)*b/107:ℝ):ℂ)*Complex.I))/(106:ℂ)=(-1:ℂ)/106 := by
  intro a ha
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 107))
  have hζ : IsPrimitiveRoot ζ 107 := Complex.isPrimitiveRoot_exp_of_coprime a 107 (by decide) ha
  have hexp (b : ℕ) : Complex.exp (((2 * Real.pi * (a : ℝ) * b / 107 : ℝ) : ℂ) * Complex.I) =
      ζ ^ b := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hp : Nat.Prime 107 := by decide
  have hfilter : (Finset.range 107).filter (fun b => Nat.Coprime b 107) =
      (Finset.range 107).erase 0 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    constructor
    · rintro ⟨hlt, hn⟩
      exact ⟨fun hb => hn (hb ▸ dvd_zero 107), hlt⟩
    · rintro ⟨hb, hlt⟩
      exact ⟨hlt, Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hb) hlt⟩
  have hsum := hζ.geom_sum_eq_zero (by decide : 1 < 107)
  rw [← Finset.sum_erase_add (Finset.range 107) (fun b => ζ ^ b)
    (by decide : 0 ∈ Finset.range 107), pow_zero] at hsum
  rw [hfilter]
  simp_rw [hexp]
  rw [eq_neg_of_add_eq_zero_left hsum]
