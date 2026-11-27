import Mathlib

/-!
# QP: `L-quadratic-primes-gauss-split-representation`

Every prime `p ≡ 1 mod 4` has a *unique* representation `p = a² + b²` with `0 < a ≤ b`.

Existence is Mathlib's Fermat two-squares theorem (`Nat.Prime.sq_add_sq`). Uniqueness:
if `a² + b² = a'² + b'² = p`, then `a/b` and `a'/b'` are both roots of `X² + 1` in the
field `ZMod p`, hence `a/b = ± a'/b'`. Equality of the first kind gives `a b' = a' b`,
and coprimality of `a, b` then forces `(a, b) = (a', b')`; the second kind gives
`p | a b' + a' b`, and the identity
`(a² + b²)(a'² + b'²) = (a a' - b b')² + (a b' + a' b)²`
then forces `a' = b, b' = a`, contradicting `p` odd.

Self-contained, Mathlib only.
-/

open scoped BigOperators

/-- **QP: split representation.** Existence and uniqueness of `p = a² + b²`. -/
theorem Conjectures.QuadraticPrimes.GaussSplitRepresentation :
    ∀ p : ℕ, p.Prime → p % 4 = 1 →
      ∃ a b : ℕ, (0 < a ∧ a ≤ b ∧ a ^ 2 + b ^ 2 = p) ∧
        ∀ a' b' : ℕ, 0 < a' → a' ≤ b' → a' ^ 2 + b' ^ 2 = p → a' = a ∧ b' = b := by
  intro p hp hp4
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  -- existence from Fermat's two-squares theorem
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := p) (by omega : p % 4 ≠ 3)
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      subst h
      have hyp : y ^ 2 = p := by simpa using hxy
      have hdiv : y ∣ p := ⟨y, by rw [← hyp]; ring⟩
      rcases hp.eq_one_or_self_of_dvd y hdiv with h1 | h1
      · rw [h1] at hyp
        norm_num at hyp
        omega
      · rw [h1] at hyp
        nlinarith
    · exact h
  have hy0 : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · exfalso
      subst h
      have hyp : x ^ 2 = p := by simpa using hxy
      have hdiv : x ∣ p := ⟨x, by rw [← hyp]; ring⟩
      rcases hp.eq_one_or_self_of_dvd x hdiv with h1 | h1
      · rw [h1] at hyp
        norm_num at hyp
        omega
      · rw [h1] at hyp
        nlinarith
    · exact h
  -- uniqueness for a fixed ordered pair
  have key : ∀ a b : ℕ, 0 < a → a ≤ b → a ^ 2 + b ^ 2 = p →
      ∀ a' b' : ℕ, 0 < a' → a' ≤ b' → a' ^ 2 + b' ^ 2 = p → a' = a ∧ b' = b := by
    intro a b ha hab hsq a' b' ha' hab' hsq'
    have hb0 : 0 < b := lt_of_lt_of_le ha hab
    have hb'0 : 0 < b' := lt_of_lt_of_le ha' hab'
    have ha_lt_p : a < p := by nlinarith [hsq, hb0, hp2]
    have hb_lt_p : b < p := by nlinarith [hsq, ha, hb0]
    have ha'_lt_p : a' < p := by nlinarith [hsq', hb'0, hp2]
    have hb'_lt_p : b' < p := by nlinarith [hsq', ha', hb'0]
    -- `a, b` are coprime
    have hcop : Nat.Coprime a b := by
      have hdvd : Nat.gcd a b ∣ a ^ 2 + b ^ 2 := by
        have h1 : Nat.gcd a b ∣ a ^ 2 := by
          simpa [pow_two] using dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) a
        have h2 : Nat.gcd a b ∣ b ^ 2 := by
          simpa [pow_two] using dvd_mul_of_dvd_left (Nat.gcd_dvd_right a b) b
        exact dvd_add h1 h2
      rw [hsq] at hdvd
      have hle : Nat.gcd a b ≤ a := Nat.gcd_le_left b ha
      rcases hp.eq_one_or_self_of_dvd (Nat.gcd a b) hdvd with h1 | h1
      · exact h1
      · omega
    -- the two roots `a/b`, `a'/b'` of `X² + 1` in `ZMod p`
    have hb_ne : (b : ZMod p) ≠ 0 := by
      intro hc
      have hdvd : p ∣ b := (CharP.cast_eq_zero_iff (ZMod p) p b).mp hc
      have hle : p ≤ b := Nat.le_of_dvd hb0 hdvd
      omega
    have hb'_ne : (b' : ZMod p) ≠ 0 := by
      intro hc
      have hdvd : p ∣ b' := (CharP.cast_eq_zero_iff (ZMod p) p b').mp hc
      have hle : p ≤ b' := Nat.le_of_dvd hb'0 hdvd
      omega
    have hroot : ((a : ZMod p) / (b : ZMod p)) ^ 2 + 1 = 0 := by
      have h : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
        have hzero : ((a ^ 2 + b ^ 2 : ℕ) : ZMod p) = 0 := by
          rw [hsq]
          exact ZMod.natCast_self p
        simpa using hzero
      rw [div_pow]
      field_simp
      linear_combination h
    have hroot' : ((a' : ZMod p) / (b' : ZMod p)) ^ 2 + 1 = 0 := by
      have h : (a' : ZMod p) ^ 2 + (b' : ZMod p) ^ 2 = 0 := by
        have hzero : ((a' ^ 2 + b' ^ 2 : ℕ) : ZMod p) = 0 := by
          rw [hsq']
          exact ZMod.natCast_self p
        simpa using hzero
      rw [div_pow]
      field_simp
      linear_combination h
    have hfac : (((a : ZMod p) / (b : ZMod p)) - ((a' : ZMod p) / (b' : ZMod p))) *
        (((a : ZMod p) / (b : ZMod p)) + ((a' : ZMod p) / (b' : ZMod p))) = 0 := by
      have hd : ((a : ZMod p) / (b : ZMod p)) ^ 2 - ((a' : ZMod p) / (b' : ZMod p)) ^ 2 = 0 := by
        linear_combination hroot - hroot'
      calc (((a : ZMod p) / (b : ZMod p)) - ((a' : ZMod p) / (b' : ZMod p))) *
            (((a : ZMod p) / (b : ZMod p)) + ((a' : ZMod p) / (b' : ZMod p)))
          = ((a : ZMod p) / (b : ZMod p)) ^ 2 - ((a' : ZMod p) / (b' : ZMod p)) ^ 2 := by ring
        _ = 0 := hd
    -- product bounds
    have ha2 : 2 * a ^ 2 ≤ p := by nlinarith [hsq, hab]
    have hb'2 : b' ^ 2 ≤ p := by nlinarith [hsq', ha']
    have ha'2 : 2 * a' ^ 2 ≤ p := by nlinarith [hsq', hab']
    have hb2 : b ^ 2 ≤ p := by nlinarith [hsq, ha]
    have hab'_lt : a * b' < p := by
      have h3 : 2 * (a * b') ^ 2 ≤ p * p := by
        have h1 : 2 * a ^ 2 * b' ^ 2 ≤ p * b' ^ 2 := Nat.mul_le_mul_right (b' ^ 2) ha2
        have h2 : p * b' ^ 2 ≤ p * p := Nat.mul_le_mul_left p hb'2
        calc 2 * (a * b') ^ 2 = 2 * a ^ 2 * b' ^ 2 := by ring
          _ ≤ p * b' ^ 2 := h1
          _ ≤ p * p := h2
      by_contra hge
      push_neg at hge
      have hp2' : p * p ≤ (a * b') * (a * b') := Nat.mul_le_mul hge hge
      have hX2 : (a * b') * (a * b') ≤ 0 := by nlinarith only [h3, hp2']
      have hX0 : a * b' = 0 := by
        have hzero : (a * b') * (a * b') = 0 := le_antisymm hX2 (Nat.zero_le _)
        rcases Nat.mul_eq_zero.mp hzero with hz | hz <;> exact hz
      omega
    have ha'b_lt : a' * b < p := by
      have h3 : 2 * (a' * b) ^ 2 ≤ p * p := by
        have h1 : 2 * a' ^ 2 * b ^ 2 ≤ p * b ^ 2 := Nat.mul_le_mul_right (b ^ 2) ha'2
        have h2 : p * b ^ 2 ≤ p * p := Nat.mul_le_mul_left p hb2
        calc 2 * (a' * b) ^ 2 = 2 * a' ^ 2 * b ^ 2 := by ring
          _ ≤ p * b ^ 2 := h1
          _ ≤ p * p := h2
      by_contra hge
      push_neg at hge
      have hp2' : p * p ≤ (a' * b) * (a' * b) := Nat.mul_le_mul hge hge
      have hX2 : (a' * b) * (a' * b) ≤ 0 := by nlinarith only [h3, hp2']
      have hX0 : a' * b = 0 := by
        have hzero : (a' * b) * (a' * b) = 0 := le_antisymm hX2 (Nat.zero_le _)
        rcases Nat.mul_eq_zero.mp hzero with hz | hz <;> exact hz
      omega
    rcases mul_eq_zero.mp hfac with heq | heq
    · -- equal roots: `a b' = a' b`
      have hcross : ((a : ZMod p) / (b : ZMod p)) = ((a' : ZMod p) / (b' : ZMod p)) := by
        linear_combination heq
      have hEqZ : ((a : ZMod p) * (b' : ZMod p)) = ((a' : ZMod p) * (b : ZMod p)) := by
        have h1 : ((a : ZMod p) / (b : ZMod p)) * ((b : ZMod p) * (b' : ZMod p)) =
            (a : ZMod p) * (b' : ZMod p) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hb_ne]
        have h2 : ((a' : ZMod p) / (b' : ZMod p)) * ((b : ZMod p) * (b' : ZMod p)) =
            (a' : ZMod p) * (b : ZMod p) := by
          rw [mul_comm ((b : ZMod p)) ((b' : ZMod p)), ← mul_assoc,
            div_mul_cancel₀ _ hb'_ne]
        calc (a : ZMod p) * (b' : ZMod p)
            = ((a : ZMod p) / (b : ZMod p)) * ((b : ZMod p) * (b' : ZMod p)) := h1.symm
          _ = ((a' : ZMod p) / (b' : ZMod p)) * ((b : ZMod p) * (b' : ZMod p)) := by rw [hcross]
          _ = (a' : ZMod p) * (b : ZMod p) := h2
      have hmod : (a * b') % p = (a' * b) % p := by
        have hcast : ((a * b' : ℕ) : ZMod p) = ((a' * b : ℕ) : ZMod p) := by
          push_cast
          exact hEqZ
        exact (ZMod.natCast_eq_natCast_iff' (a * b') (a' * b) p).mp hcast
      have hprod : a * b' = a' * b := by
        have h1 : (a * b') % p = a * b' := Nat.mod_eq_of_lt hab'_lt
        have h2 : (a' * b) % p = a' * b := Nat.mod_eq_of_lt ha'b_lt
        rw [h1, h2] at hmod
        exact hmod
      have hda : a ∣ a' := by
        have h : a ∣ a' * b := by
          rw [← hprod]
          exact dvd_mul_right a b'
        exact hcop.dvd_of_dvd_mul_right h
      obtain ⟨k, hk⟩ := hda
      have hkb : b' = b * k := by
        have h : a * b' = a * (b * k) := by
          rw [hprod, hk]
          ring
        exact Nat.eq_of_mul_eq_mul_left ha h
      have hk1 : k = 1 := by
        have hsqk : (a ^ 2 + b ^ 2) * k ^ 2 = (a ^ 2 + b ^ 2) * 1 := by
          calc (a ^ 2 + b ^ 2) * k ^ 2 = (a * k) ^ 2 + (b * k) ^ 2 := by ring
            _ = a' ^ 2 + b' ^ 2 := by rw [← hk, ← hkb]
            _ = p := hsq'
            _ = a ^ 2 + b ^ 2 := hsq.symm
            _ = (a ^ 2 + b ^ 2) * 1 := by ring
        have ha2pos : 0 < a ^ 2 := pow_pos ha 2
        have hpos : 0 < a ^ 2 + b ^ 2 := lt_of_lt_of_le ha2pos (Nat.le_add_right _ _)
        have hk2 : k ^ 2 = 1 := Nat.eq_of_mul_eq_mul_left hpos hsqk
        nlinarith only [hk2]
      refine ⟨?_, ?_⟩
      · rw [hk, hk1, mul_one]
      · rw [hkb, hk1, mul_one]
    · -- opposite roots: `a b' + a' b ≡ 0` mod `p`
      have hcross : ((a : ZMod p) / (b : ZMod p)) = -((a' : ZMod p) / (b' : ZMod p)) := by
        linear_combination heq
      have hEqZ : ((a : ZMod p) * (b' : ZMod p)) + ((a' : ZMod p) * (b : ZMod p)) = 0 := by
        have h1 : ((a : ZMod p) / (b : ZMod p)) * ((b : ZMod p) * (b' : ZMod p)) =
            (a : ZMod p) * (b' : ZMod p) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hb_ne]
        have h2 : ((a' : ZMod p) / (b' : ZMod p)) * ((b : ZMod p) * (b' : ZMod p)) =
            (a' : ZMod p) * (b : ZMod p) := by
          rw [mul_comm ((b : ZMod p)) ((b' : ZMod p)), ← mul_assoc,
            div_mul_cancel₀ _ hb'_ne]
        have hsum : ((a : ZMod p) * (b' : ZMod p)) + ((a' : ZMod p) * (b : ZMod p)) =
            (((a : ZMod p) / (b : ZMod p)) + ((a' : ZMod p) / (b' : ZMod p))) *
              ((b : ZMod p) * (b' : ZMod p)) := by
          rw [add_mul, h1, h2]
        calc ((a : ZMod p) * (b' : ZMod p)) + ((a' : ZMod p) * (b : ZMod p))
            = (((a : ZMod p) / (b : ZMod p)) + ((a' : ZMod p) / (b' : ZMod p))) *
                ((b : ZMod p) * (b' : ZMod p)) := hsum
          _ = 0 := by rw [hcross]; ring
      have hcast : ((a * b' + a' * b : ℕ) : ZMod p) = 0 := by
        push_cast
        exact hEqZ
      have hdvd : p ∣ a * b' + a' * b := (CharP.cast_eq_zero_iff (ZMod p) p _).mp hcast
      have hsum_pos : 0 < a * b' + a' * b :=
        lt_of_lt_of_le (Nat.mul_pos ha hb'0) (Nat.le_add_right _ _)
      have hsum_lt : a * b' + a' * b < 2 * p := by
        have h1 : a * b' < p := hab'_lt
        have h2 : a' * b < p := ha'b_lt
        omega
      have hsum_eq : a * b' + a' * b = p := by
        obtain ⟨t, ht⟩ := hdvd
        have htpos : 0 < t := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · rw [h0, mul_zero] at ht
            omega
          · exact h0
        have htlt : t < 2 := by
          have hs : p * t < 2 * p := by rw [ht] at hsum_lt; exact hsum_lt
          nlinarith only [hs, htpos, hp2]
        have ht1 : t = 1 := by omega
        rw [ht, ht1, mul_one]
      -- AM-GM: the sum `a b' + a' b = p` attains equality in both estimates
      have ham1 : 2 * (a * b') ≤ a ^ 2 + b' ^ 2 := by
        have hZ : (2 : ℤ) * ((a : ℤ) * (b' : ℤ)) ≤ (a : ℤ) ^ 2 + (b' : ℤ) ^ 2 := by
          nlinarith only [sq_nonneg ((a : ℤ) - (b' : ℤ))]
        have hZ' : ((2 * (a * b') : ℕ) : ℤ) ≤ ((a ^ 2 + b' ^ 2 : ℕ) : ℤ) := by
          push_cast
          linarith [hZ]
        exact_mod_cast hZ'
      have ham2 : 2 * (a' * b) ≤ a' ^ 2 + b ^ 2 := by
        have hZ : (2 : ℤ) * ((a' : ℤ) * (b : ℤ)) ≤ (a' : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
          nlinarith only [sq_nonneg ((a' : ℤ) - (b : ℤ))]
        have hZ' : ((2 * (a' * b) : ℕ) : ℤ) ≤ ((a' ^ 2 + b ^ 2 : ℕ) : ℤ) := by
          push_cast
          linarith [hZ]
        exact_mod_cast hZ'
      have hsum2 : 2 * (a * b') + 2 * (a' * b) = 2 * p := by
        omega
      have hbound : 2 * (a * b') + 2 * (a' * b) ≤ 2 * p := by
        calc 2 * (a * b') + 2 * (a' * b) ≤ (a ^ 2 + b' ^ 2) + (a' ^ 2 + b ^ 2) :=
              Nat.add_le_add ham1 ham2
          _ = 2 * p := by omega
      have heq1 : 2 * (a * b') = a ^ 2 + b' ^ 2 := by omega
      have heq2 : 2 * (a' * b) = a' ^ 2 + b ^ 2 := by omega
      -- equality in AM-GM forces `a = b'` and `a' = b`
      have hb'a : b' = a := by
        have hZ : (2 : ℤ) * ((a : ℤ) * (b' : ℤ)) = (a : ℤ) ^ 2 + (b' : ℤ) ^ 2 := by
          have hcast : ((2 * (a * b') : ℕ) : ℤ) = ((a ^ 2 + b' ^ 2 : ℕ) : ℤ) := by
            rw [heq1]
          push_cast at hcast
          exact hcast
        have hsq0 : ((a : ℤ) - (b' : ℤ)) ^ 2 = 0 := by linear_combination -hZ
        have hzero : (a : ℤ) - (b' : ℤ) = 0 :=
          (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq0
        have : (a : ℤ) = (b' : ℤ) := by linarith only [hzero]
        exact_mod_cast this.symm
      have ha'b : a' = b := by
        have hZ : (2 : ℤ) * ((a' : ℤ) * (b : ℤ)) = (a' : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
          have hcast : ((2 * (a' * b) : ℕ) : ℤ) = ((a' ^ 2 + b ^ 2 : ℕ) : ℤ) := by
            rw [heq2]
          push_cast at hcast
          exact hcast
        have hsq0 : ((a' : ℤ) - (b : ℤ)) ^ 2 = 0 := by linear_combination -hZ
        have hzero : (a' : ℤ) - (b : ℤ) = 0 :=
          (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq0
        have : (a' : ℤ) = (b : ℤ) := by linarith only [hzero]
        exact_mod_cast this
      have hba : b ≤ a := by
        have h1 : a' ≤ b' := hab'
        rwa [ha'b, hb'a] at h1
      have hab_eq : a = b := le_antisymm hab hba
      refine ⟨?_, ?_⟩
      · rw [ha'b, hab_eq]
      · rw [hb'a, hab_eq]
  rcases le_total x y with hle | hle
  · exact ⟨x, y, ⟨hx0, hle, hxy⟩, key x y hx0 hle hxy⟩
  · refine ⟨y, x, ⟨hy0, hle, ?_⟩, key y x hy0 hle ?_⟩
    · rw [add_comm]
      exact hxy
    · rw [add_comm]
      exact hxy
