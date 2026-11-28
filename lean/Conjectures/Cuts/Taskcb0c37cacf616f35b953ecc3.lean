import Mathlib

open Finset Filter
open scoped Topology

private def primesAP (d a X : ℕ) :=
  (Ioc 0 X).filter (fun p => Nat.Prime p ∧ p % d = a)

private def selected (A : Set ℕ) [DecidablePred (· ∈ A)] (d a X : ℕ) :=
  (Ioc 0 X).filter (fun p => Nat.Prime p ∧ p % d = a ∧ p ∈ A)

private theorem progression_sum (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA : ∀ p ∈ A, Nat.Prime p) (d a L : ℕ) (hd : 0 < d) (ha : a < d) (ha0 : 0 < a) :
    ∑ p ∈ selected A d a (d*L), Real.log p =
      ∑ j ∈ range L, if d*j+a ∈ A then Real.log (d*j+a : ℕ) else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij' (fun p _ => p / d) (fun j _ => d*j+a)
  · intro p hp
    obtain ⟨hpx, _, hpa, hpA⟩ := mem_filter.mp hp
    have hm := Nat.mod_add_div p d
    have hlim := (mem_Ioc.mp hpx).2
    have hne : p ≠ d*L := by
      intro h
      simp [h] at hpa
      omega
    exact mem_filter.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.mul_comm]; omega)),
      by rwa [← hpa, Nat.add_comm, Nat.mod_add_div]⟩
  · intro j hj
    obtain ⟨hj, hjA⟩ := mem_filter.mp hj
    have hjl := mem_range.mp hj
    have hb : d*(j+1) ≤ d*L := Nat.mul_le_mul_left _ hjl
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by positivity, by nlinarith⟩,
      hA _ hjA, by simp [Nat.mul_comm d j, Nat.mod_eq_of_lt ha], hjA⟩
  · intro p hp
    have hr := (mem_filter.mp hp).2.2.1
    rw [← hr, Nat.add_comm, Nat.mod_add_div]
  · intro j hj
    simp [Nat.mul_add_div hd, Nat.div_eq_of_lt ha]

  · intro p hp
    have hr := (mem_filter.mp hp).2.2.1
    rw [← hr, Nat.add_comm (d*(p/d)), Nat.mod_add_div]

private theorem counting_to_weight (A : Set ℕ) [DecidablePred (· ∈ A)] (hA : ∀ p ∈ A, Nat.Prime p)
    (d a : ℕ) (t : ℝ) (hd : 2 ≤ d) (ha : a < d) (hcop : a.Coprime d)
    (_ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hdens : ∀ e : ℝ, 0 < e → ∃ T : ℕ, ∀ X ≥ T,
      (t-e) * ((primesAP d a X).card : ℝ) ≤ (selected A d a X).card) :
    ∀ ζ : ℝ, 0 < ζ → ∃ T : ℕ, ∀ L ≥ T, (t-ζ)*((d*L : ℕ):ℝ) ≤
      (d.totient:ℝ)*∑ j ∈ range L, if d*j+a ∈ A then Real.log (d*j+a : ℕ) else 0 := by
  intro ζ hζ
  have hd0 : 0 < d := by omega
  let : NeZero d := ⟨hd0.ne'⟩
  have ha0 : 0 < a := by
    by_contra! h
    obtain rfl : a = 0 := by omega
    have : d = 1 := by simpa using hcop
    omega
  let φ : ℝ := d.totient
  have hφ : 0 < φ := by dsimp [φ]; exact_mod_cast Nat.totient_pos.mpr hd0
  have sum_nonneg (L : ℕ) : 0 ≤ ∑ p ∈ selected A d a (d*L), Real.log (p:ℝ) :=
    sum_nonneg (fun p hp => Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.1.one_le))
  by_cases hz : t ≤ ζ
  · exact ⟨0, fun L _ => by rw [← progression_sum A hA d a L hd0 ha ha0]
                            exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans
                              (mul_nonneg hφ.le (sum_nonneg L))⟩
  let e := ζ/3
  have he : 0 < e := by dsimp [e]; positivity
  have hte : 0 ≤ t-e := by dsimp [e]; linarith
  have hsmall : 0 < e/φ := div_pos he hφ
  have hlim := (Chebyshev.tendsto_sum_log_prime_modEq_div_atTop hcop).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbelow : (1-e)/φ < φ⁻¹ := by rw [← one_div]; exact div_lt_div_of_pos_right (by linarith) hφ
  have hb := hlim.eventually_const_lt hbelow
  have herr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((Chebyshev.isLittleO_card_prime_with_mul_log_sum_prime_log_with
        (fun p => p % d = a ∧ p ∈ A)).bound hsmall)
  obtain ⟨T₀,h₀⟩ := hdens e he
  obtain ⟨T₁,h₁⟩ := eventually_atTop.mp hb
  obtain ⟨T₂,h₂⟩ := eventually_atTop.mp herr
  refine ⟨max 1 (max T₀ (max T₁ T₂)), ?_⟩
  intro L hL
  let X := d*L
  have hLX : L ≤ X := Nat.le_mul_of_pos_left L hd0
  have hX1 : 1 ≤ X := by omega
  have hX : (0:ℝ) < X := by exact_mod_cast hX1
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ X by exact_mod_cast hX1)
  let P := primesAP d a X
  let V := selected A d a X
  have htheta : (1-e)/φ * (X:ℝ) ≤ ∑ p ∈ P, Real.log (p:ℝ) := by
    have h := h₁ X (by omega)
    change _ < (∑ p ∈ Ioc 0 ⌊(X:ℝ)⌋₊ with p.Prime ∧ p ≡ a [MOD d], Real.log (p:ℝ)) / X at h
    simpa [P,primesAP,Nat.ModEq,Nat.mod_eq_of_lt ha] using (lt_div_iff₀ hX).mp h |>.le
  have hmass : (V.card:ℝ) * Real.log X - ∑ p ∈ V, Real.log (p:ℝ) ≤ (e/φ)*X := by
    have h := h₂ X (by omega)
    simpa [V, selected, Real.norm_eq_abs, abs_of_nonneg hX.le] using (le_abs_self _).trans h
  have hcount := mul_le_mul_of_nonneg_right (h₀ X (by omega)) hlog
  have hlogP : (∑ p ∈ P, Real.log (p:ℝ)) ≤ P.card * Real.log X := by
    simpa [nsmul_eq_mul] using (sum_le_card_nsmul P (fun p => Real.log (p:ℝ)) (Real.log X)
      (fun p hp => Real.log_le_log (by exact_mod_cast (mem_filter.mp hp).2.1.pos)
        (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2)))
  have hcomp : (t-e) * ((1-e)/φ*(X:ℝ)) ≤ (V.card:ℝ)*Real.log X := by
    exact (mul_le_mul_of_nonneg_left (htheta.trans hlogP) hte).trans (by simpa [P,V,mul_assoc] using hcount)
  have hlow : (t-e) * ((1-e)/φ*(X:ℝ)) - (e/φ)*X ≤ ∑ p ∈ V, Real.log (p:ℝ) := by linarith
  rw [← progression_sum A hA d a L hd0 ha ha0]
  change (t-ζ)*(X:ℝ) ≤ φ * ∑ p ∈ V, Real.log (p:ℝ)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hlow hφ.le)
  have hcoeff : t-ζ ≤ (t-e)*(1-e)-e := by
    dsimp [e]; nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hζ.le, sq_nonneg ζ]
  convert mul_le_mul_of_nonneg_right hcoeff hX.le using 1
  field_simp

theorem Conjectures.Cuts.Taskcb0c37cacf616f35b953ecc3 : (∀ (x1 : Set ℕ) [x2 : DecidablePred fun (x2 : ℕ) => x2 ∈ x1],   (∀ x3 ∈ x1, Nat.Prime x3) →     ∀ (x4 x5 : ℕ) (x6 : ℝ),       (2 : ℕ) ≤ x4 →         x5 < x4 →           x5.Coprime x4 →             (0 : ℝ) ≤ x6 →               x6 ≤ (1 : ℝ) →                 have x12 : ℕ → Finset ℕ := fun (x12 : ℕ) => {x13 ∈ Finset.Icc (1 : ℕ) x12 | Nat.Prime x13 ∧ x13 % x4 = x5};                 (∀ (x13 : ℝ), (0 : ℝ) < x13 → ∃ (x15 : ℕ), ∀ x16 ≥ x15, (x6 - x13) * ↑(x12 x16).card ≤ ↑{x18 ∈ x12 x16 | x18 ∈ x1}.card) → ∀ (x14 : ℝ), (0 : ℝ) < x14 → ∃ (x16 : ℕ), ∀ x17 ≥ x16, (x6 - x14) * ↑(x4 * x17) ≤ ↑x4.totient * ∑ x19 ∈ Finset.range x17, if x4 * x19 + x5 ∈ x1 then Real.log ↑(x4 * x19 + x5) else (0 : ℝ)) := by
  intro A inst hA d a t hd ha hcop ht ht1 primes hdens
  apply counting_to_weight A hA d a t hd ha hcop ht ht1
  intro ε hε
  obtain ⟨T, hT⟩ := hdens ε hε
  refine ⟨T, fun X hX => ?_⟩
  have hp : primes X = primesAP d a X := by
    ext n
    simp [primes,primesAP]
    omega
  have hv : (primes X).filter (· ∈ A) = selected A d a X := by
    rw [hp]
    ext n
    simp [primesAP,selected,and_assoc]
  simpa only [← hp, ← hv] using hT X hX
