import Mathlib

open Finset

-- child 1 zh: 用限制在等差数列上的完整指数和与有限几何和逼近主弧傅里叶系数。
-- child 1 en: Approximate a major-arc Fourier coefficient by a complete progression exponential sum and a finite geometric sum.
-- child 2 zh: 在主弧以外，统一控制每个既约类上的归一化素数傅里叶系数。
-- child 2 en: Bound the normalized prime Fourier coefficient uniformly outside the major arcs.
-- child 3 zh: 控制完整剩余类指数和，并在模数有公因子时证明它消去。
-- child 3 en: Bound the complete restricted residue sum, with exact cancellation when the moduli share a prime factor.

set_option maxHeartbeats 900000 in
theorem Conjectures.Cuts.Cut8e51da253643170a4a367a56
    (major :
      ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε →
        ∃ T : ℕ, ∀ (N : ℕ) [NeZero N], T ≤ N →
          ∀ a : ℕ, a < d → a.Coprime d →
            let R := (Nat.log 2 (d*N+2))^18
            let e := fun u : ℝ => Complex.exp ((-2:ℂ)*(Real.pi:ℂ)*Complex.I*(u:ℂ))
            let ν := fun x : ZMod N =>
              if Nat.Prime (d*x.val+a) then (d.totient:ℝ)/(d:ℝ)*Real.log (d*x.val+a:ℕ) else 0
            let F := fun r : ZMod N =>
              (∑ x : ZMod N, (ν x:ℂ) *
                Complex.exp (-2*(Real.pi:ℂ)*Complex.I*((r*x).val:ℂ)/(N:ℂ)))/(N:ℂ)
            ∀ (r : ZMod N) (q b : ℕ), 1 ≤ q → q ≤ R → b ≤ q → b.Coprime q →
              |(r.val:ℝ)/(N:ℝ)-(b:ℝ)/(q:ℝ)| ≤ (2*(R:ℝ))/((q:ℝ)*(N:ℝ)) →
              let C := (d.totient:ℂ)/((d*q).totient:ℂ) *
                ∑ j ∈ (Finset.range q).filter (fun j => (d*j+a).Coprime (d*q)),
                  e ((b:ℝ)*(j:ℝ)/(q:ℝ))
              let K := (∑ j ∈ Finset.range N,
                e ((j:ℝ)*((r.val:ℝ)/(N:ℝ)-(b:ℝ)/(q:ℝ))))/(N:ℂ)
              ‖F r-C*K‖ ≤ ε)
    (minor :
      ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε →
        ∃ T : ℕ, ∀ (N : ℕ) [NeZero N], T ≤ N →
          ∀ a : ℕ, a < d → a.Coprime d →
            let R := (Nat.log 2 (d*N+2))^18
            let ν := fun x : ZMod N =>
              if Nat.Prime (d*x.val+a) then (d.totient:ℝ)/(d:ℝ)*Real.log (d*x.val+a:ℕ) else 0
            let F := fun r : ZMod N =>
              (∑ x : ZMod N, (ν x:ℂ) *
                Complex.exp (-2*(Real.pi:ℂ)*Complex.I*((r*x).val:ℂ)/(N:ℂ)))/(N:ℂ)
            ∀ r : ZMod N,
              (¬ ∃ q b : ℕ, 1 ≤ q ∧ q ≤ R ∧ b ≤ q ∧ b.Coprime q ∧
                |(r.val:ℝ)/(N:ℝ)-(b:ℝ)/(q:ℝ)| ≤ (2*(R:ℝ))/((q:ℝ)*(N:ℝ))) →
              ‖F r‖ ≤ ε)
    (coeff :
      ∀ d : ℕ, 2 ≤ d → ∀ a : ℕ, a < d → a.Coprime d →
        ∀ q : ℕ, 0 < q → ∀ b : ℕ, b ≤ q → b.Coprime q →
          let e := fun u : ℝ => Complex.exp ((-2:ℂ)*(Real.pi:ℂ)*Complex.I*(u:ℂ))
          ‖∑ j ∈ (Finset.range q).filter (fun j => (d*j+a).Coprime (d*q)),
            e ((b:ℝ)*(j:ℝ)/(q:ℝ))‖ ≤ if d.Coprime q then (1:ℝ) else 0) :
    ∀ (x1 : ℕ),   (0 : ℕ) < x1 →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℕ),           (0 : ℕ) < x5 ∧             (2 : ℕ) * x1 ∣ x5 ∧               ∃ (x6 : ℕ),                 ∀ (x7 : ℕ) [x8 : NeZero x7],                   x6 ≤ x7 →                     ∀ x10 < x5,                       x10.Coprime x5 →                         have x13 : ZMod x7 → ℝ := fun (x13 : ZMod x7) => if Nat.Prime (x5 * x13.val + x10) then ↑x5.totient / ↑x5 * Real.log ↑(x5 * x13.val + x10) else (0 : ℝ);                         have x14 : (ZMod x7 → ℝ) → ZMod x7 → ℂ := fun (x14 : ZMod x7 → ℝ) (x15 : ZMod x7) => (∑ x16 : ZMod x7, ↑(x14 x16) * Complex.exp ((-2 : ℂ) * ↑Real.pi * Complex.I * ↑(x15 * x16).val / ↑x7)) / ↑x7;                         ∀ (x15 : ZMod x7), ‖x14 (fun (x16 : ZMod x7) => x13 x16 - (1 : ℝ)) x15‖ ≤ x3 := by
  classical
  have exists_modulus (W : ℕ) (hW : 0 < W) (ε : ℝ) (hε : 0 < ε) :
      ∃ d : ℕ, 2 ≤ d ∧ 2*W ∣ d ∧
        ∀ q : ℕ, 1 < q → d.Coprime q → 1 / (q.totient : ℝ) ≤ ε := by
    obtain ⟨k, hk⟩ := exists_nat_gt (1/ε)
    let d := (2*W) * (k+2).factorial
    have hd : 2 ≤ d := by
      calc
        2 ≤ 2*W := by omega
        _ ≤ d := by
          simpa only [d, Nat.mul_one] using
            Nat.mul_le_mul_left (2*W) (show 1 ≤ (k+2).factorial from Nat.factorial_pos _)
    refine ⟨d,hd,dvd_mul_right _ _,?_⟩
    intro q hq hc
    let p := q.minFac
    have hp : p.Prime := Nat.minFac_prime (ne_of_gt hq)
    have hpq : p ∣ q := Nat.minFac_dvd q
    have hpLarge : k+2 < p := by
      by_contra! hsmall
      have hpf : p ∣ (k+2).factorial := Nat.dvd_factorial hp.pos hsmall
      have hpd : p ∣ d := dvd_mul_of_dvd_right hpf (2*W)
      have hcp := (hc.coprime_dvd_left hpd).coprime_dvd_right hpq
      exact hp.ne_one ((Nat.coprime_self p).mp hcp)
    have htpos : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    have hptot : p.totient ≤ q.totient :=
      Nat.le_of_dvd htpos (Nat.totient_dvd_of_dvd hpq)
    rw [Nat.totient_prime hp] at hptot
    have hktot : k ≤ q.totient := by omega
    have hqt : 0 < (q.totient : ℝ) := by exact_mod_cast htpos
    have hinv : 1/ε ≤ (q.totient : ℝ) := hk.le.trans (by exact_mod_cast hktot)
    exact (div_le_iff₀ hqt).mpr (by
      have h := (div_le_iff₀ hε).mp hinv
      simpa only [mul_comm] using h)

  let uniformPhase (u : ℝ) : ℂ :=
    Complex.exp ((-2 : ℂ)*(Real.pi : ℂ)*Complex.I*(u : ℂ))

  let uniformKernel (N : ℕ) (t : ℝ) : ℂ :=
    (∑ j ∈ Finset.range N, uniformPhase ((j : ℝ)*t))/(N : ℂ)

  let uniformFt {N : ℕ} [NeZero N] (h : ZMod N → ℝ) (r : ZMod N) : ℂ :=
    (∑ x : ZMod N, (h x : ℂ) *
      Complex.exp ((-2 : ℂ)*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)

  have uniformKernelNorm :
      ∀ (N : ℕ) [NeZero N] (t : ℝ), ‖uniformKernel N t‖ ≤ 1 := by
    intro N _ t
    have hphase (u : ℝ) : ‖uniformPhase u‖ = 1 := by
      unfold uniformPhase
      rw [show (-2 : ℂ)*(Real.pi : ℂ)*Complex.I*(u : ℂ) =
        (((-2*Real.pi*u : ℝ) : ℂ)*Complex.I) by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    unfold uniformKernel
    rw [norm_div, Complex.norm_natCast, div_le_one (by exact_mod_cast NeZero.pos N)]
    exact (norm_sum_le _ _).trans (by simp [hphase])

  have uniformCharacterSum :
      ∀ (N : ℕ) [NeZero N] (r : ZMod N),
        (∑ x : ZMod N, ZMod.stdAddChar (-(r*x))) = if r=0 then (N : ℂ) else 0 := by
    intro N _ r
    simpa only [mul_comm _ (-r), neg_mul, neg_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      AddChar.sum_mulShift (-r) (ZMod.isPrimitive_stdAddChar N)

  have uniformSumRangeToZMod :
      ∀ (N : ℕ) [NeZero N] (G : ZMod N → ℂ),
        (∑ j ∈ Finset.range N, G (j : ZMod N)) = ∑ x : ZMod N, G x := by
    intro N _ G
    refine Finset.sum_bij' (fun j _ => (j : ZMod N)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · intro j _
      exact Finset.mem_univ _
    · intro x _
      exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro j hj
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)
    · intro x _
      exact ZMod.natCast_zmod_val x
    · intro j _
      rfl

  have uniformPhaseAtGrid :
      ∀ (N : ℕ) [NeZero N] (r : ZMod N) (j b : ℕ),
        uniformPhase ((j : ℝ)*((r.val : ℝ)/(N : ℝ)-(b : ℝ))) =
          ZMod.stdAddChar (-(r*(j : ZMod N))) := by
    intro N _ r j b
    have hcast : -(r*(j : ZMod N)) = ((-((r.val*j : ℕ) : ℤ) : ℤ) : ZMod N) := by
      rw [Int.cast_neg, Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.stdAddChar_coe]
    have hexp : (-2 : ℂ)*(Real.pi : ℂ)*Complex.I *
        ((((j : ℝ)*((r.val : ℝ)/(N : ℝ)-(b : ℝ))) : ℝ) : ℂ) =
        2*(Real.pi : ℂ)*Complex.I * ((-((r.val*j : ℕ) : ℤ) : ℤ) : ℂ)/(N : ℂ) +
          (((j*b : ℕ) : ℤ) : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by
      push_cast
      ring
    unfold uniformPhase
    rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

  have uniformKernelGrid :
      ∀ (N : ℕ) [NeZero N] (r : ZMod N) (b : ℕ),
        uniformKernel N ((r.val : ℝ)/(N : ℝ)-(b : ℝ)) = if r=0 then 1 else 0 := by
    intro N _ r b
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    unfold uniformKernel
    simp_rw [uniformPhaseAtGrid N r]
    rw [uniformSumRangeToZMod N (fun x => ZMod.stdAddChar (-(r*x))), uniformCharacterSum N]
    by_cases hr : r=0 <;> simp [hr, hN]

  have uniformPhaseEqCharacter :
      ∀ (N : ℕ) [NeZero N] (a : ZMod N),
        Complex.exp ((-2 : ℂ)*(Real.pi : ℂ)*Complex.I*(a.val : ℂ)/(N : ℂ)) =
          ZMod.stdAddChar (-a) := by
    intro N _ a
    rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_neg]
    congr 1
    ring

  have uniformFtSubOne :
      ∀ {N : ℕ} [NeZero N] (ν : ZMod N → ℝ) (r : ZMod N),
        uniformFt (fun x => ν x-1) r = uniformFt ν r - (if r=0 then 1 else 0) := by
    intro N _ ν r
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    simp only [uniformFt, uniformPhaseEqCharacter N, Complex.ofReal_sub, Complex.ofReal_one, sub_mul,
      one_mul, Finset.sum_sub_distrib, sub_div, uniformCharacterSum N]
    by_cases hr : r=0 <;> simp [hr, hN]

  let e (u : ℝ) : ℂ :=
    Complex.exp ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I * (u : ℂ))

  let raw (d a q b : ℕ) : ℂ :=
    ∑ j ∈ (Finset.range q).filter (fun j => (d * j + a).Coprime (d * q)),
      e ((b : ℝ) * (j : ℝ) / (q : ℝ))

  let C (d a q b : ℕ) : ℂ :=
    (d.totient : ℂ) / ((d * q).totient : ℂ) * raw d a q b

  have coeff_one (d a b : ℕ) (hd : 0 < d) (ha : a.Coprime d) :
      C d a 1 b = 1 := by
    have htot : (d.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hd).ne'
    simp [C, raw, e, Finset.range_one, ite_eq_left ha, htot]

  have coeff_small (d a q b : ℕ) (ε : ℝ) (hd : 0 < d) (hq : 1 < q)
      (hε : 0 < ε) (hsmall : d.Coprime q → 1 / (q.totient : ℝ) ≤ ε)
      (hraw : ‖raw d a q b‖ ≤ if d.Coprime q then 1 else 0) :
      ‖C d a q b‖ ≤ ε := by
    dsimp only [C]
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    by_cases hcop : d.Coprime q
    · have hdtot : 0 < (d.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hd
      have hqtot : 0 < (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr ((Nat.zero_lt_succ 0).trans hq)
      have hraw' : ‖raw d a q b‖ ≤ 1 := by
        simpa only [ite_eq_left hcop] using hraw
      rw [Nat.totient_mul hcop, Nat.cast_mul, div_mul_eq_div_div, div_self hdtot.ne']
      exact (mul_le_of_le_one_right (div_nonneg zero_le_one hqtot.le) hraw').trans (hsmall hcop)
    · have hraw' : ‖raw d a q b‖ ≤ 0 := by
        simpa only [ite_eq_right hcop] using hraw
      rw [le_antisymm hraw' (norm_nonneg _), mul_zero]
      exact hε.le

  intro W hW β hβ
  obtain ⟨d, hd, hDiv, hSmall⟩ := exists_modulus W hW (β / 2) (by positivity)
  obtain ⟨T₁, hMajor⟩ := major d hd (β / 2) (by positivity)
  obtain ⟨T₂, hMinor⟩ := minor d hd (β / 2) (by positivity)
  let T := max T₁ T₂
  refine ⟨d, by omega, hDiv, T, ?_⟩
  intro N nz hNT a ha haCo
  dsimp only
  intro r
  let ν (x : ZMod N) : ℝ :=
    if Nat.Prime (d * x.val + a) then
      (d.totient : ℝ) / (d : ℝ) * Real.log (d * x.val + a : ℕ)
    else 0
  let R := (Nat.log 2 (d * N + 2)) ^ 18
  have hR : 1 ≤ R := by
    have hLog : 1 ≤ Nat.log 2 (d * N + 2) :=
      Nat.le_log_of_pow_le (by decide) (by simp)
    exact Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hNT₁ : T₁ ≤ N := (le_max_left _ _).trans hNT
  have hNT₂ : T₂ ≤ N := (le_max_right _ _).trans hNT
  have hHalf : β / 2 ≤ β := by linarith only [hβ]
  have majorAt (t : ZMod N) (q b : ℕ)
      (hq : 1 ≤ q) (hRq : q ≤ R) (hb : b ≤ q) (hCo : b.Coprime q)
      (hClose : |(t.val : ℝ) / N - (b : ℝ) / q| ≤ (2 * (R : ℝ)) / ((q : ℝ) * N)) :
      ‖uniformFt ν t - C d a q b * uniformKernel N ((t.val : ℝ) / N - (b : ℝ) / q)‖ ≤ β / 2 :=
    hMajor N hNT₁ a ha haCo t q b hq hRq hb hCo hClose
  change ‖uniformFt (fun x => ν x - 1) r‖ ≤ β
  rw [uniformFtSubOne ν r]
  by_cases hr : r = 0
  · subst r
    have hClose : |((0 : ZMod N).val : ℝ) / N - (0 : ℝ) / (1 : ℕ)| ≤
        (2 * (R : ℝ)) / (((1 : ℕ) : ℝ) * N) := by
      simp only [ZMod.val_zero, Nat.cast_zero, zero_div, sub_self, abs_zero, Nat.cast_one, one_mul]
      positivity
    have h := majorAt (0 : ZMod N) 1 0 (by decide) hR (by decide) (by decide) hClose
    have hc := coeff_one d a 0 (by omega) haCo
    apply le_trans _ hHalf
    simpa only [Nat.cast_one, div_one, hc, uniformKernelGrid, ite_eq_left rfl, one_mul] using h
  · rw [ite_eq_right hr, sub_zero]
    by_cases hArc : ∃ q b : ℕ,
        1 ≤ q ∧ q ≤ R ∧ b ≤ q ∧ b.Coprime q ∧
          |(r.val : ℝ) / N - (b : ℝ) / q| ≤ (2 * (R : ℝ)) / ((q : ℝ) * N)
    · obtain ⟨q, b, hq, hRq, hb, hbCo, hClose⟩ := hArc
      have h := majorAt r q b hq hRq hb hbCo hClose
      by_cases hqOne : q = 1
      · subst q
        apply le_trans _ hHalf
        simpa only [Nat.cast_one, div_one, uniformKernelGrid, ite_eq_right hr, mul_zero, sub_zero] using h
      · let main := C d a q b * uniformKernel N ((r.val : ℝ) / N - (b : ℝ) / q)
        have hCoef : ‖C d a q b‖ ≤ β / 2 :=
          coeff_small d a q b (β / 2) (by omega) (by omega) (by positivity)
            (hSmall q (by omega)) (coeff d hd a ha haCo q (by omega) b hb hbCo)
        have hMain : ‖main‖ ≤ β / 2 := by
          rw [show main = C d a q b * uniformKernel N ((r.val : ℝ) / N - (b : ℝ) / q) by rfl, norm_mul]
          calc
            _ ≤ (β / 2) * 1 :=
              mul_le_mul hCoef (uniformKernelNorm N _) (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
        calc
          ‖uniformFt ν r‖ = ‖(uniformFt ν r - main) + main‖ := by rw [sub_add_cancel]
          _ ≤ ‖uniformFt ν r - main‖ + ‖main‖ := norm_add_le _ _
          _ ≤ β / 2 + β / 2 := add_le_add h hMain
          _ = β := by ring
    · exact (hMinor N hNT₂ a ha haCo r hArc).trans hHalf
