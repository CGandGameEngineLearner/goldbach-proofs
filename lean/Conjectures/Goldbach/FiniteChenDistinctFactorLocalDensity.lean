import Mathlib

/-! PREPUB finite 组：chen distinct factor local density（模素数计数）。 -/

theorem Conjectures.Goldbach.FiniteChenDistinctFactorLocalDensity :
    ∀ (ℓ r n : ℕ), ℓ.Prime → let B := (Finset.range ℓ).filter (fun v => v=0 ∨ (r*v ) % ℓ = n % ℓ); B.card = (if ℓ∣r then (if ℓ∣n then ℓ else 1) else (if ℓ∣n then 1 else 2)) := by
  intro ℓ r n hℓ
  dsimp only
  by_cases hr : ℓ ∣ r
  · by_cases hn : ℓ ∣ n
    · have hfilter : (Finset.range ℓ).filter (fun v => v=0 ∨ (r*v ) % ℓ = n % ℓ) = Finset.range ℓ := by
        apply Finset.filter_true_of_mem
        intro v hv
        right
        have h1 : (r*v) % ℓ = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hr v)
        have h2 : n % ℓ = 0 := Nat.mod_eq_zero_of_dvd hn
        rw [h1, h2]
      rw [hfilter, Finset.card_range, if_pos hr, if_pos hn]
    · have hfilter : (Finset.range ℓ).filter (fun v => v=0 ∨ (r*v ) % ℓ = n % ℓ) = {0} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro h
          rcases h with ⟨hv, h0 | heq⟩
          · exact h0
          · exfalso
            apply hn
            have h1 : (r*v) % ℓ = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hr v)
            have h2 : n % ℓ = 0 := by rw [← heq, h1]
            exact Nat.dvd_of_mod_eq_zero h2
        · intro h0
          subst h0
          exact ⟨hℓ.pos, Or.inl rfl⟩
      rw [hfilter, Finset.card_singleton, if_pos hr, if_neg hn]
  · by_cases hn : ℓ ∣ n
    · have hfilter : (Finset.range ℓ).filter (fun v => v=0 ∨ (r*v ) % ℓ = n % ℓ) = {0} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro h
          rcases h with ⟨hv, h0 | heq⟩
          · exact h0
          · have hn0 : n % ℓ = 0 := Nat.mod_eq_zero_of_dvd hn
            have h1 : (r*v) % ℓ = 0 := by rw [heq, hn0]
            have hdvd : ℓ ∣ r*v := Nat.dvd_of_mod_eq_zero h1
            have hdv : ℓ ∣ v := (hℓ.coprime_iff_not_dvd.mpr hr).dvd_of_dvd_mul_left hdvd
            exact Nat.eq_zero_of_dvd_of_lt hdv hv
        · intro h0
          subst h0
          exact ⟨hℓ.pos, Or.inl rfl⟩
      rw [hfilter, Finset.card_singleton, if_neg hr, if_pos hn]
    · haveI : Fact ℓ.Prime := ⟨hℓ⟩
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have hr0 : (r : ZMod ℓ) ≠ 0 := by
        intro h
        exact hr ((ZMod.natCast_eq_zero_iff r ℓ).mp h)
      have hn0 : (n : ZMod ℓ) ≠ 0 := by
        intro h
        exact hn ((ZMod.natCast_eq_zero_iff n ℓ).mp h)
      let w : ZMod ℓ := (n : ZMod ℓ) / (r : ZMod ℓ)
      let v0 : ℕ := w.val
      have hv0cast : (v0 : ZMod ℓ) = w := ZMod.natCast_zmod_val w
      have hmul : (r : ZMod ℓ) * (v0 : ZMod ℓ) = (n : ZMod ℓ) := by
        rw [hv0cast]
        dsimp only [w]
        field_simp
      have hmod : (r * v0) % ℓ = n % ℓ := by
        have hcast : ((r * v0 : ℕ) : ZMod ℓ) = (n : ZMod ℓ) := by
          push_cast
          exact hmul
        exact (ZMod.natCast_eq_natCast_iff' (r*v0) n ℓ).mp hcast
      have hv0lt : v0 < ℓ := ZMod.val_lt w
      have hv0ne : v0 ≠ 0 := by
        intro h
        apply hn0
        rw [← hmul, h]
        simp
      have hfilter : (Finset.range ℓ).filter (fun v => v=0 ∨ (r*v ) % ℓ = n % ℓ) = {0, v0} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h
          rcases h with ⟨hv, h0 | heq⟩
          · exact Or.inl h0
          · right
            have hmodv : (r*v) % ℓ = (r*v0) % ℓ := by rw [heq, hmod]
            have hcast : ((r*v : ℕ) : ZMod ℓ) = ((r*v0 : ℕ) : ZMod ℓ) :=
              (ZMod.natCast_eq_natCast_iff' (r*v) (r*v0) ℓ).mpr hmodv
            push_cast at hcast
            have hvv : (v : ZMod ℓ) = (v0 : ZMod ℓ) := mul_left_cancel₀ hr0 hcast
            have hvvmod : v % ℓ = v0 % ℓ := (ZMod.natCast_eq_natCast_iff' v v0 ℓ).mp hvv
            rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hv0lt] at hvvmod
            exact hvvmod
        · intro h
          rcases h with h | h
          · subst h
            exact ⟨hℓ.pos, Or.inl rfl⟩
          · subst h
            exact ⟨hv0lt, Or.inr hmod⟩
      have hnot : (0:ℕ) ∉ ({v0} : Finset ℕ) := by
        simp only [Finset.mem_singleton]
        exact fun h => hv0ne h.symm
      have hcard : ({0, v0} : Finset ℕ).card = 2 := by
        rw [Finset.card_insert_of_notMem hnot]
        simp
      rw [hfilter, if_neg hr, if_neg hn]
      exact hcard

theorem PEqualNP.Outside.L_goldbach_finite_chen_distinct_factor_local_density :
    ∀ (ℓ r n : ℕ), ℓ.Prime → let B := (Finset.range ℓ).filter (fun v => v=0 ∨ (r*v ) % ℓ = n % ℓ); B.card = (if ℓ∣r then (if ℓ∣n then ℓ else 1) else (if ℓ∣n then 1 else 2)) :=
  Conjectures.Goldbach.FiniteChenDistinctFactorLocalDensity
