import Mathlib

-- The denominator band and annulus come from proposal #4258 and discussion #3806.
-- child 1 zh: 在所给分母带内，不含 p 的容许除数至少有常数倍 Q(N) 个。
-- child 1 en: The specified band contains at least a constant times Q(N) eligible divisors.
-- child 2 zh: 在整个分母带内，所给环带上的核积分至少是 N 的固定正比例。
-- child 2 en: Throughout the denominator band the kernel integral is bounded below by a fixed positive multiple of N.

theorem Conjectures.Cuts.Cut327fe2ad28b79602e5771b8f
    (hDensity : (by
      classical
      let n := fun (p y : ℕ) =>
        ∏ r ∈ (Finset.Icc 2 y).filter (fun r => Nat.Prime r ∧ r ≠ p), r
      let Q := fun N : ℕ => (Nat.log 2 (N+2))^2
      exact ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ∃ a : ℝ, 0 < a ∧ ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
        let N := n p y
        let D := N.divisors.filter (fun d => Q N < p*d ∧ p*d ≤ 2*Q N)
        a * (Q N : ℝ) ≤ (D.card : ℝ)))
    (hKernel : (by
      let Q := fun N : ℕ => (Nat.log 2 (N+2))^2
      let mass := fun (N q : ℕ) =>
        let lo := (Q N : ℝ) / ((q : ℝ) * (N : ℝ))
        2 * intervalIntegral
          (fun t : ℝ => (Real.sin (Real.pi * ((N : ℝ) + 1) * t) / Real.sin (Real.pi * t))^2)
          lo (lo * (N : ℝ)^((1 : ℝ) / 6)) MeasureTheory.volume
      exact ∃ b : ℝ, 0 < b ∧ ∀ N : ℕ, 64 ≤ N → ∀ q : ℕ, Q N < q → q ≤ 2 * Q N →
        b * (N : ℝ) ≤ mass N q)) :
  (by
    classical
    let n := fun (p y : ℕ) => ∏ r ∈ (Finset.Icc 2 y).filter (fun r => Nat.Prime r ∧ r ≠ p), r
    let Q := fun N : ℕ => (Nat.log 2 (N+2))^2
    let mass := fun (N q : ℕ) =>
      let lo := (Q N : ℝ) / ((q:ℝ)*(N:ℝ))
      2 * intervalIntegral (fun t : ℝ => (Real.sin (Real.pi*((N:ℝ)+1)*t) / Real.sin (Real.pi*t))^2) lo (lo*(N:ℝ)^((1:ℝ)/6)) MeasureTheory.volume
    exact ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
      let N := n p y
      let D := N.divisors.filter (fun d => Q N < p*d ∧ p*d ≤ 2*Q N)
      c*(N:ℝ) ≤ ∑ d ∈ D, ((d.totient:ℝ)/(((p*d).totient:ℝ)^2)) * mass N (p*d)) := by
  classical
  dsimp only at hDensity hKernel ⊢
  intro p hp hp3
  obtain ⟨a, ha, Y, hY⟩ := hDensity p hp hp3
  obtain ⟨b, hb, hbmass⟩ := hKernel
  -- The totient factor separates because p was excluded from the prime product.
  have coefficient (p d Q : ℕ)
      (hp : p.Prime) (hp3 : 3 ≤ p) (hd : 0 < d)
      (hc : p.Coprime d) (hbound : p*d ≤ 2*Q) :
      (p : ℝ) / (2*((p : ℝ)-1)^2*(Q : ℝ)) ≤
        (d.totient : ℝ) / (((p*d).totient : ℝ)^2) := by
    have hpd : 0 < p*d := Nat.mul_pos hp.pos hd
    have hQ : (0 : ℝ) < (Q : ℝ) := by
      exact_mod_cast (show 0 < Q by omega)
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hpm : 0 < (p : ℝ)-1 := by linarith only [hpR]
    have hφ : 0 < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
    have htot : ((p*d).totient : ℝ) = ((p : ℝ)-1)*(d.totient : ℝ) := by
      rw [Nat.totient_mul hc, Nat.totient_prime hp, Nat.cast_mul,
        Nat.cast_sub hp.one_le, Nat.cast_one]
    have hsmall : (p : ℝ)*(d.totient : ℝ) ≤ 2*(Q : ℝ) := by
      exact_mod_cast (Nat.mul_le_mul_left p (Nat.totient_le d)).trans hbound
    rw [htot, mul_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ = ((p : ℝ)*(d.totient : ℝ))*(((p : ℝ)-1)^2*(d.totient : ℝ)) := by ring
      _ ≤ (2*(Q : ℝ))*(((p : ℝ)-1)^2*(d.totient : ℝ)) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = _ := by ring
  let K : ℝ := (p : ℝ) / (2 * ((p : ℝ) - 1)^2)
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hpm : 0 < (p : ℝ) - 1 := by linarith only [hpR]
  have hK : 0 < K := by dsimp [K]; positivity
  let c : ℝ := a * b * K
  refine ⟨c, mul_pos (mul_pos ha hb) hK, max Y 71, ?_⟩
  intro y hy
  let pool := (Finset.Icc 2 y).filter (fun r => Nat.Prime r ∧ r ≠ p)
  let N : ℕ := ∏ r ∈ pool, r
  let Q := (Nat.log 2 (N+2))^2
  let D := N.divisors.filter (fun d => Q < p*d ∧ p*d ≤ 2*Q)
  let mass (q : ℕ) : ℝ :=
    let lo := (Q : ℝ) / ((q : ℝ) * (N : ℝ))
    2 * intervalIntegral
      (fun t : ℝ => (Real.sin (Real.pi * ((N : ℝ) + 1) * t) / Real.sin (Real.pi * t))^2)
      lo (lo * (N : ℝ)^((1 : ℝ) / 6)) MeasureTheory.volume
  change c * (N : ℝ) ≤ ∑ d ∈ D, ((d.totient : ℝ) / (((p*d).totient : ℝ)^2)) * mass (p*d)
  have hpool (r : ℕ) (hr : r ∈ pool) : r.Prime ∧ r ≠ p := (Finset.mem_filter.mp hr).2
  have hNpos : 0 < N := Finset.prod_pos (fun r hr => (hpool r hr).1.pos)
  have hN : 64 ≤ N := by
    have hy71 : 71 ≤ y := (le_max_right Y 71).trans hy
    have hlarge : ∃ r : ℕ, 64 ≤ r ∧ r ∈ pool := by
      by_cases h : p = 67
      · refine ⟨71, by decide, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, hy71⟩, ?_⟩⟩
        exact ⟨by decide, by omega⟩
      · refine ⟨67, by decide, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, by omega⟩, ?_⟩⟩
        exact ⟨by decide, Ne.symm h⟩
    obtain ⟨r, hr, hrpool⟩ := hlarge
    exact hr.trans (Nat.le_of_dvd hNpos (Finset.dvd_prod_of_mem id hrpool))
  have hQ : 0 < (Q : ℝ) := by
    exact_mod_cast (pow_pos (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ N + 2)) 2)
  have hpN : p.Coprime N := by
    refine Nat.coprime_prod_right_iff.mpr (fun r hr => hp.coprime_iff_not_dvd.mpr ?_)
    exact ((Nat.prime_dvd_prime_iff_eq hp (hpool r hr).1).not.mpr (Ne.symm (hpool r hr).2))
  have hterm (d : ℕ) (hdD : d ∈ D) :
      (K / (Q : ℝ)) * (b * (N : ℝ)) ≤
        ((d.totient : ℝ) / (((p*d).totient : ℝ)^2)) * mass (p*d) := by
    obtain ⟨hdN, hband⟩ := Finset.mem_filter.mp hdD
    have hdvd : d ∣ N := (Nat.mem_divisors.mp hdN).1
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hNpos
    have hcoef : K / (Q : ℝ) ≤ (d.totient : ℝ) / (((p*d).totient : ℝ)^2) := by
      dsimp only [K]
      rw [div_div]
      exact coefficient p d Q hp hp3 hd (hpN.coprime_dvd_right hdvd) hband.2
    have hm : b * (N : ℝ) ≤ mass (p*d) := hbmass N hN (p*d) hband.1 hband.2
    exact mul_le_mul hcoef hm (by positivity) (by positivity)
  have hcount : a * (Q : ℝ) ≤ (D.card : ℝ) :=
    hY y ((le_max_left Y 71).trans hy)
  calc
    c * (N : ℝ) = (a * (Q : ℝ)) * ((K / (Q : ℝ)) * (b * (N : ℝ))) := by
      dsimp [c]
      field_simp [hQ.ne']
    _ ≤ (D.card : ℝ) * ((K / (Q : ℝ)) * (b * (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = ∑ _d ∈ D, (K / (Q : ℝ)) * (b * (N : ℝ)) := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm
