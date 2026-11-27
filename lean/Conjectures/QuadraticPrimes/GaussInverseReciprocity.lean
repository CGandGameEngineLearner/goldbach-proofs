import Mathlib

theorem Conjectures.QuadraticPrimes.GaussInverseReciprocity :
    ∀ a b p r v : ℕ, 0<a → a≤b → p.Prime → p=a^2+b^2 →
      r<p → v<b → (b*r)%p=a%p → (a*v)%b=1%b →
      ∃ j : ℤ, (r : ℝ)/p + (v : ℝ)/b = (j : ℝ) + (a : ℝ)/((b : ℝ)*p) := by
  intro a b p r v ha hab hp hpeq hr hv hbr hav
  have hb_pos : 0 < b := lt_of_lt_of_le ha hab
  have hp_pos : 0 < p := hp.pos
  have ha_lt_p : a < p := by
    have hb2 : b ≤ b ^ 2 := by
      have h := Nat.mul_le_mul_left b hb_pos
      simpa [pow_two, mul_comm] using h
    have ha2 : 1 ≤ a ^ 2 := by
      have h := Nat.mul_le_mul ha ha
      simpa [pow_two] using h
    omega
  have hb_lt_p : b < p := by
    have hb2 : b ≤ b ^ 2 := by
      have h := Nat.mul_le_mul_left b hb_pos
      simpa [pow_two, mul_comm] using h
    have ha2 : 1 ≤ a ^ 2 := by
      have h := Nat.mul_le_mul ha ha
      simpa [pow_two] using h
    omega
  have ha_mod_p : a % p = a := Nat.mod_eq_of_lt ha_lt_p
  -- `p ∣ b*r - a` over `ℤ`
  have hbr' : (b * r) % p = a := by rw [hbr, ha_mod_p]
  have hbr_eq : b * r = (b * r) / p * p + a := by
    have h := Nat.mod_add_div (b * r) p
    rw [hbr', mul_comm p ((b * r) / p)] at h
    omega
  have hdvdP : (p : ℤ) ∣ ((b : ℤ) * (r : ℤ) - (a : ℤ)) := by
    refine ⟨((b * r) / p : ℕ), ?_⟩
    have h : ((b * r : ℕ) : ℤ) = (p : ℤ) * ((b * r / p : ℕ) : ℤ) + (a : ℤ) := by
      conv_lhs => rw [hbr_eq]
      rw [Nat.cast_add, Nat.cast_mul]
      ring
    push_cast at h ⊢
    linarith
  -- `b ∣ a*v - 1` over `ℤ`
  have hdvdB : (b : ℤ) ∣ ((a : ℤ) * (v : ℤ) - 1) := by
    rcases Nat.eq_or_lt_of_le (show 1 ≤ b from hb_pos) with hb1 | hb2
    · subst hb1
      simp
    · have hav' : (a * v) % b = 1 := by
        rw [hav, Nat.mod_eq_of_lt (by omega : 1 < b)]
      have hav_eq : a * v = (a * v) / b * b + 1 := by
        have h := Nat.mod_add_div (a * v) b
        rw [hav', mul_comm b ((a * v) / b)] at h
        omega
      refine ⟨((a * v) / b : ℕ), ?_⟩
      have h : ((a * v : ℕ) : ℤ) = (b : ℤ) * ((a * v / b : ℕ) : ℤ) + 1 := by
        conv_lhs => rw [hav_eq]
        rw [Nat.cast_add, Nat.cast_mul]
        ring
      push_cast at h ⊢
      linarith
  have hpZ : (p : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    rw [hpeq]
    push_cast
    ring
  -- `b ∣ b*r + p*v - a`
  have hdvdB2 : (b : ℤ) ∣ ((b : ℤ) * (r : ℤ) + (p : ℤ) * (v : ℤ) - (a : ℤ)) := by
    obtain ⟨t, ht⟩ := hdvdB
    refine ⟨(r : ℤ) + (b : ℤ) * (v : ℤ) + (a : ℤ) * t, ?_⟩
    have hBt : (a : ℤ) * ((b : ℤ) * t) = (a : ℤ) ^ 2 * (v : ℤ) - (a : ℤ) := by
      rw [← ht]
      ring
    rw [hpZ]
    calc (b : ℤ) * (r : ℤ) + ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) * (v : ℤ) - (a : ℤ)
        = (b : ℤ) * (r : ℤ) + (b : ℤ) ^ 2 * (v : ℤ)
            + ((a : ℤ) ^ 2 * (v : ℤ) - (a : ℤ)) := by ring
      _ = (b : ℤ) * (r : ℤ) + (b : ℤ) ^ 2 * (v : ℤ) + (a : ℤ) * ((b : ℤ) * t) := by
            rw [hBt]
      _ = (b : ℤ) * ((r : ℤ) + (b : ℤ) * (v : ℤ) + (a : ℤ) * t) := by ring
  -- `p ∣ b*r + p*v - a`
  have hdvdP2 : (p : ℤ) ∣ ((b : ℤ) * (r : ℤ) + (p : ℤ) * (v : ℤ) - (a : ℤ)) := by
    obtain ⟨s, hs⟩ := hdvdP
    refine ⟨s + (v : ℤ), ?_⟩
    calc (b : ℤ) * (r : ℤ) + (p : ℤ) * (v : ℤ) - (a : ℤ)
        = ((b : ℤ) * (r : ℤ) - (a : ℤ)) + (p : ℤ) * (v : ℤ) := by ring
      _ = (p : ℤ) * s + (p : ℤ) * (v : ℤ) := by rw [hs]
      _ = (p : ℤ) * (s + (v : ℤ)) := by ring
  have hcop : Nat.Coprime b p := by
    refine (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hd
    have hle : p ≤ b := Nat.le_of_dvd hb_pos hd
    omega
  have hcopZ : IsCoprime (b : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hcop
  have hdvd : ((b : ℤ) * (p : ℤ)) ∣ ((b : ℤ) * (r : ℤ) + (p : ℤ) * (v : ℤ) - (a : ℤ)) :=
    hcopZ.mul_dvd hdvdB2 hdvdP2
  obtain ⟨j, hj⟩ := hdvd
  refine ⟨j, ?_⟩
  have hcastZ : (b : ℤ) * (r : ℤ) + (p : ℤ) * (v : ℤ) = (j : ℤ) * ((b : ℤ) * (p : ℤ)) + (a : ℤ) := by
    have hj' : (b : ℤ) * (r : ℤ) + (p : ℤ) * (v : ℤ) - (a : ℤ)
        = (j : ℤ) * ((b : ℤ) * (p : ℤ)) := by
      rw [hj]
      ring
    linarith
  have hcast : (b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ) = (j : ℝ) * ((b : ℝ) * (p : ℝ)) + (a : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hcastZ
    push_cast at h
    simpa using h
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb_pos.ne'
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmain : (r : ℝ) / (p : ℝ) + (v : ℝ) / (b : ℝ)
      = ((b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ)) / ((b : ℝ) * (p : ℝ)) := by
    rw [div_add_div _ _ hp0 hb0]
    congr 1
    · ring
    · ring
  rw [hmain, hcast]
  field_simp
