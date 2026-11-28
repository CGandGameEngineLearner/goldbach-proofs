import Mathlib
import PEqualNP.Outside.L_goldbach_arc_major_floor

namespace GoldbachColorFixedAP

open Finset Filter
open scoped Topology

noncomputable section

-- The logarithmic prime progression estimate is from repository PR 316.
private theorem classMass_eq_theta (Y d a : ℕ) :
    GoldbachMajorArc.classMass (Y + 1) d a =
      ∑ p ∈ (Finset.Icc 1 Y).filter (fun p => Nat.Prime p ∧ p % d = a),
        Real.log (p : ℝ) := by
  have hsets : Finset.Ioc 0 Y = Finset.Icc 1 Y := by
    ext p
    simp [Nat.succ_le_iff]
  rw [GoldbachMajorArc.classMass, Nat.range_succ_eq_Icc_zero, sum_filter,
    ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le Y), hsets, sum_filter]
  simp only [GoldbachMajorArc.primeWeight, Nat.not_prime_zero, ite_false, ite_self, zero_add]
  apply sum_congr rfl
  intro p _
  by_cases hp : Nat.Prime p <;> by_cases ha : p % d = a <;> simp [hp, ha]

-- This comparison follows the logarithmic bound in repository PR 316.
private theorem nat_log_two_le {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h₂ := Real.log_two_gt_d9
  have h := Real.natLog_le_logb n 2
  simp only [Nat.cast_ofNat, Real.logb] at h
  refine h.trans ((div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr ?_)
  nlinarith only [mul_nonneg hL (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]

private theorem eventually_log_le_rpow (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ Y : ℕ in atTop, Real.log Y ≤ c * (Y : ℝ)^r := by
  have h := ((isLittleO_log_rpow_atTop hr).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound hc
  filter_upwards [h] with Y hY
  change ‖Real.log (Y : ℝ)‖ ≤ c * ‖(Y : ℝ)^r‖ at hY
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Y) _)] at hY
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hY)

theorem fixed_ap_theta_lower (d a : ℕ) (hd : 0 < d) (ha : a < d)
    (hcop : a.Coprime d) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ Y ≥ T, (1 - ε) * (Y : ℝ) ≤
      (d.totient : ℝ) * ∑ p ∈ (Finset.Icc 1 Y).filter (fun p => Nat.Prime p ∧ p % d = a),
        Real.log (p : ℝ) := by
  obtain ⟨M, hM, Y₀, hY₀, hAP⟩ :=
    GoldbachMajorArc.prime_progression_error 1 1 (by norm_num) (by norm_num)
  let φ : ℝ := d.totient
  have hφ : 0 < φ := by
    change (0 : ℝ) < (d.totient : ℝ)
    exact_mod_cast Nat.totient_pos.mpr hd
  let e := ε / (3 * φ)
  have he : 0 < e := div_pos hε (by positivity)
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  let c := e / (2 * (Real.log d + 1))
  have hcden : 0 < 2 * (Real.log d + 1) := by positivity
  have hc : 0 < c := div_pos he hcden
  have hcoef : 2 * Real.log d * c ≤ e := by
    dsimp only [c]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hcden).mpr (by nlinarith only [he.le])
  have hcast : Tendsto (fun Y : ℕ => (Y : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hLog := Real.tendsto_log_atTop.comp hcast
  have hlin := eventually_log_le_rpow 1 c (by norm_num) hc
  have hsqrt := eventually_log_le_rpow (1/2) (e/2) (by norm_num) (by positivity)
  apply eventually_atTop.mp
  filter_upwards [hcast.eventually_ge_atTop Y₀, hLog.eventually_ge_atTop (d : ℝ),
    hLog.eventually_ge_atTop (M / e), hlin, hsqrt]
    with Y hY hdlog hMlog hlinY hsqrtY
  change Y₀ ≤ (Y : ℝ) at hY
  change (d : ℝ) ≤ Real.log Y at hdlog
  change M / e ≤ Real.log Y at hMlog
  rw [Real.rpow_one] at hlinY
  rw [← Real.sqrt_eq_rpow] at hsqrtY
  have hY1 : (1 : ℝ) < Y := hY₀.trans_le hY
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  have hMle : M ≤ e * Real.log Y := by
    simpa only [mul_comm] using (div_le_iff₀ he).mp hMlog
  have hmain : M * (Y : ℝ) * (Real.log Y)^(-1 : ℝ) ≤ e * (Y : ℝ) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
    apply (div_le_iff₀ hlogY).mpr
    have h := mul_le_mul_of_nonneg_right hMle (Nat.cast_nonneg (α := ℝ) Y)
    nlinarith only [h]
  have hcorr : (Nat.log 2 Y : ℝ) * Real.log d ≤ e * (Y : ℝ) := by
    have hNat := nat_log_two_le (n := Y) (by exact_mod_cast hY1.le)
    calc
      _ ≤ (2 * Real.log Y) * Real.log d :=
        mul_le_mul_of_nonneg_right hNat hlogd
      _ = (2 * Real.log d) * Real.log Y := by ring
      _ ≤ (2 * Real.log d) * (c * (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left hlinY (by positivity)
      _ = (2 * Real.log d * c) * (Y : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
  have hpower : 2 * Real.sqrt Y * Real.log Y ≤ e * (Y : ℝ) := by
    calc
      _ ≤ 2 * Real.sqrt Y * ((e / 2) * Real.sqrt Y) :=
        mul_le_mul_of_nonneg_left hsqrtY (by positivity)
      _ = e * (Real.sqrt Y)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg Y)]
  have hraw := hAP Y d a hY hd (by simpa only [Real.rpow_one] using hdlog) ha hcop
  have hAbs : |GoldbachMajorArc.classMass (Y + 1) d a - (Y : ℝ) / φ| ≤
      3 * e * (Y : ℝ) :=
    hraw.trans (by linarith only [hmain, hcorr, hpower])
  have hlower : (Y : ℝ) / φ - 3 * e * (Y : ℝ) ≤ GoldbachMajorArc.classMass (Y + 1) d a := by
    linarith only [(abs_le.mp hAbs).1]
  calc
    _ = φ * ((Y : ℝ) / φ - 3 * e * (Y : ℝ)) := by
      dsimp only [e]
      field_simp [hφ.ne']
    _ ≤ φ * GoldbachMajorArc.classMass (Y + 1) d a :=
      mul_le_mul_of_nonneg_left hlower hφ.le
    _ = _ := by rw [classMass_eq_theta]

end
end GoldbachColorFixedAP

open Finset Filter Asymptotics

namespace GoldbachColorTrim

theorem eventual_log_weight_lower (d : ℕ) (hd : 0 < d) (s : ℝ) (hs : 0 < s)
    (hs1 : s < 1) :
    ∃ Y₀ : ℕ, ∀ Y ≥ Y₀, ∀ S : Finset ℕ, S ⊆ Icc 1 Y →
      (1 - s) * ((d : ℝ) * Real.log (Y : ℝ) * (S.card : ℝ) - s * (Y : ℝ)) ≤
        (d : ℝ) * ∑ p ∈ S, Real.log (p : ℝ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsmallLog : ∀ᶠ Y : ℝ in atTop, ‖Real.log Y‖ ≤ (s / (d : ℝ)) * ‖Y ^ s‖ :=
    (isLittleO_log_rpow_atTop hs).bound (by positivity)
  have hNat : ∀ᶠ Y : ℕ in atTop,
      1 ≤ Y ∧ ‖Real.log (Y : ℝ)‖ ≤ (s / (d : ℝ)) * ‖(Y : ℝ) ^ s‖ :=
    (eventually_ge_atTop 1).and
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallLog)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hNat
  refine ⟨Y₀, fun Y hY S hS => ?_⟩
  obtain ⟨hY1, hlog⟩ := hY₀ Y hY
  have hYp : 0 < (Y : ℝ) := by exact_mod_cast (show 0 < Y by omega)
  have hlog0 : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  have hpow_s : 0 ≤ (Y : ℝ) ^ s := Real.rpow_nonneg hYp.le _
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hpow_s] at hlog
  have herr : (d : ℝ) * Real.log (Y : ℝ) * (Y : ℝ) ^ (1 - s) ≤ s * (Y : ℝ) := by
    calc
      _ ≤ (d : ℝ) * ((s / (d : ℝ)) * (Y : ℝ) ^ s) * (Y : ℝ) ^ (1 - s) := by
        gcongr
      _ = s * ((Y : ℝ) ^ s * (Y : ℝ) ^ (1 - s)) := by field_simp
      _ = _ := by rw [← Real.rpow_add hYp, show s + (1 - s) = 1 by ring, Real.rpow_one]
  let R := ⌊(Y : ℝ) ^ (1 - s)⌋₊
  let small := S.filter (fun p => p ≤ R)
  let large := S.filter (fun p => ¬p ≤ R)
  have hcards : (small.card : ℝ) + (large.card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s := S) (fun p => p ≤ R))
  have hsmall : (small.card : ℝ) ≤ (Y : ℝ) ^ (1 - s) := by
    have hsub : small ⊆ Icc 1 R := by
      intro p hp
      obtain ⟨hpS, hpR⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(mem_Icc.mp (hS hpS)).1, hpR⟩
    have hcard : small.card ≤ R := by simpa using card_le_card hsub
    exact (show (small.card : ℝ) ≤ (R : ℝ) by exact_mod_cast hcard).trans
      (Nat.floor_le (Real.rpow_nonneg hYp.le _))
  have hlarge : large ⊆ S := filter_subset _ _
  have hpoint : ∀ p ∈ large, (1 - s) * Real.log (Y : ℝ) ≤ Real.log (p : ℝ) := by
    intro p hp
    have hpR : R < p := Nat.lt_of_not_ge (mem_filter.mp hp).2
    have hpPow : (Y : ℝ) ^ (1 - s) < (p : ℝ) := Nat.lt_of_floor_lt hpR
    rw [← Real.log_rpow hYp]
    exact Real.log_le_log (Real.rpow_pos_of_pos hYp _) hpPow.le
  have hsum : (1 - s) * Real.log (Y : ℝ) * (large.card : ℝ) ≤
      ∑ p ∈ S, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ large, (1 - s) * Real.log (Y : ℝ) := by
        rw [sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ p ∈ large, Real.log (p : ℝ) := sum_le_sum hpoint
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hlarge (fun p _ _ => Real.log_natCast_nonneg p)
  have herr' : (d : ℝ) * Real.log (Y : ℝ) * (small.card : ℝ) ≤ s * (Y : ℝ) :=
    (mul_le_mul_of_nonneg_left hsmall (by positivity)).trans herr
  calc
    _ ≤ (1 - s) * ((d : ℝ) * Real.log (Y : ℝ) * (S.card : ℝ) -
          (d : ℝ) * Real.log (Y : ℝ) * (small.card : ℝ)) := by gcongr
    _ = (d : ℝ) * ((1 - s) * Real.log (Y : ℝ) * (large.card : ℝ)) := by
      rw [← hcards]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hdR.le

end GoldbachColorTrim

namespace GoldbachColorAPEnum

open Finset

/-- A reduced arithmetic progression in the first full L blocks, enumerated
by the quotient of each member by the modulus. -/
theorem weighted_class_eq_progression (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA : ∀ p ∈ A, Nat.Prime p) (d a : ℕ) (hd : 2 ≤ d) (ha : a < d)
    (hc : a.Coprime d) (L : ℕ) :
    (∑ p ∈ ((Icc 1 (d*L)).filter (fun p => Nat.Prime p ∧ p % d = a)).filter (· ∈ A),
      Real.log (p : ℝ)) =
    ∑ j ∈ range L, if d*j+a ∈ A then Real.log (d*j+a : ℕ) else 0 := by
  have hdpos : 0 < d := by omega
  have hapos : 0 < a := by
    by_contra! hn
    have hz : a = 0 := by omega
    subst a
    have hd1 := (Nat.coprime_zero_left d).mp hc
    omega
  rw [← sum_filter]
  let P := ((Icc 1 (d*L)).filter (fun p => Nat.Prime p ∧ p % d = a)).filter (· ∈ A)
  let J := (range L).filter (fun j => d*j+a ∈ A)
  change (∑ p ∈ P, Real.log (p : ℝ)) = ∑ j ∈ J, Real.log (d*j+a : ℕ)
  have reconstruct (p : ℕ) (hp : p ∈ P) : d*(p/d)+a = p := by
    have hmod := (mem_filter.mp (mem_filter.mp hp).1).2.2
    have h := Nat.mod_add_div p d
    rw [hmod] at h
    simpa only [Nat.add_comm] using h
  refine sum_bij' (fun p _ => p/d) (fun j _ => d*j+a) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpIcc, _, hpmod⟩ := mem_filter.mp (mem_filter.mp hp).1
    have hmax := (mem_Icc.mp hpIcc).2
    have hlt : p < d*L := lt_of_le_of_ne hmax (by
      intro he
      rw [he, Nat.mul_mod_right] at hpmod
      omega)
    have hq : p/d < L := (Nat.div_lt_iff_lt_mul hdpos).2 (by
      simpa only [Nat.mul_comm d L] using hlt)
    exact mem_filter.mpr ⟨mem_range.mpr hq, by
      rw [reconstruct p hp]
      exact (mem_filter.mp hp).2⟩
  · intro j hj
    obtain ⟨hjL, hjA⟩ := mem_filter.mp hj
    have hup : d*j+a ≤ d*L := by
      have h := Nat.mul_le_mul_left d (Nat.succ_le_of_lt (mem_range.mp hjL))
      rw [Nat.mul_succ] at h
      omega
    have hmod : (d*j+a) % d = a := by
      rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt ha]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hup⟩,hA _ hjA,hmod⟩,hjA⟩
  · intro p hp
    exact reconstruct p hp
  · intro j _
    rw [Nat.mul_add_div hdpos, Nat.div_eq_of_lt ha, add_zero]
  · intro p hp
    rw [reconstruct p hp]

end GoldbachColorAPEnum

theorem Conjectures.Cuts.Taskcb0c37cacf616f35b953ecc3 :
      ∀ (A : Set ℕ) [DecidablePred (· ∈ A)], (∀ p ∈ A, Nat.Prime p) →
        ∀ (d a : ℕ) (t : ℝ), 2 ≤ d → a < d → a.Coprime d → 0 ≤ t → t ≤ 1 →
          let primes := fun N : ℕ =>
            (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % d = a)
          (∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
            (t - ε) * ((primes N).card : ℝ) ≤
              (((primes N).filter (· ∈ A)).card : ℝ)) →
          ∀ ζ : ℝ, 0 < ζ → ∃ T : ℕ, ∀ L ≥ T,
            (t - ζ) * ((d * L : ℕ) : ℝ) ≤
              (d.totient : ℝ) * ∑ j ∈ Finset.range L,
                if d * j + a ∈ A then Real.log (d * j + a : ℕ) else 0 := by
  intro A instA hA d a t hd ha hCo ht₀ ht₁
  dsimp only
  intro density ζ hζ
  let primes (Y : ℕ) :=
    (Finset.Icc 1 Y).filter (fun p => Nat.Prime p ∧ p % d = a)
  have hdpos : 0 < d := by omega
  have hφpos : 0 < d.totient := Nat.totient_pos.mpr hdpos
  have hφR : 0 ≤ (d.totient : ℝ) := by positivity
  by_cases htz : t ≤ ζ
  · refine ⟨0, ?_⟩
    intro L _
    have hsum : 0 ≤ ∑ j ∈ Finset.range L,
        if d * j + a ∈ A then Real.log (d * j + a : ℕ) else 0 := by
      apply Finset.sum_nonneg
      intro j _
      split
      · exact Real.log_natCast_nonneg _
      · exact le_rfl
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htz) (Nat.cast_nonneg _)).trans
      (mul_nonneg hφR hsum)

  let s := min (ζ / 8) (1 / 8)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hs1 : s < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hsζ : 4 * s ≤ ζ := by
    have hh : s ≤ ζ / 8 := min_le_left _ _
    linarith only [hh, hζ]
  have hts : 0 ≤ t - s := by linarith only [lt_of_not_ge htz, hsζ, hs]
  obtain ⟨Tθ, hTheta⟩ := GoldbachColorFixedAP.fixed_ap_theta_lower d a hdpos ha hCo s hs
  obtain ⟨TA, hColorCount⟩ := density s hs
  obtain ⟨TS, hTrim⟩ := GoldbachColorTrim.eventual_log_weight_lower d.totient hφpos s hs hs1
  let T := max 2 (max Tθ (max TA TS))
  refine ⟨T, ?_⟩
  intro L hL
  let Y := d * L
  let P := primes Y
  let Q := P.filter (fun p => p ∈ A)
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLY : L ≤ Y := by
    simpa only [one_mul] using Nat.mul_le_mul_right L (show 1 ≤ d by omega)
  have hTθ : Tθ ≤ Y := ((le_max_left _ _).trans ((le_max_right _ _).trans hL)).trans hLY
  have hTA : TA ≤ Y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))).trans hLY
  have hTS : TS ≤ Y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))).trans hLY
  have hLogY : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  have hY : 0 ≤ (Y : ℝ) := Nat.cast_nonneg _
  have hθUpper : (∑ p ∈ P, Real.log (p : ℝ)) ≤ (P.card : ℝ) * Real.log (Y : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ P, Real.log (Y : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hI := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
        exact Real.log_le_log (by exact_mod_cast (show 0 < p by omega)) (by exact_mod_cast hI.2)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hMass : (1 - s) * (Y : ℝ) ≤ (d.totient : ℝ) * Real.log (Y : ℝ) * (P.card : ℝ) := by
    have hlo := hTheta Y hTθ
    calc
      _ ≤ (d.totient : ℝ) * ∑ p ∈ P, Real.log (p : ℝ) := hlo
      _ ≤ (d.totient : ℝ) * ((P.card : ℝ) * Real.log (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left hθUpper hφR
      _ = _ := by ring
  have hCol : (t - s) * (P.card : ℝ) ≤ (Q.card : ℝ) := hColorCount Y hTA
  have hQMass : (t - s) * ((1 - s) * (Y : ℝ)) ≤
      (d.totient : ℝ) * Real.log (Y : ℝ) * (Q.card : ℝ) := by
    calc
      _ ≤ (t - s) * ((d.totient : ℝ) * Real.log (Y : ℝ) * (P.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hMass hts
      _ = ((d.totient : ℝ) * Real.log (Y : ℝ)) * ((t - s) * (P.card : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCol (mul_nonneg hφR hLogY)
  have hQ : Q ⊆ Finset.Icc 1 Y :=
    fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hQTrim := hTrim Y hTS Q hQ
  have hAstep : t - 2 * s ≤ (t - s) * (1 - s) := by
    have h := mul_le_mul_of_nonneg_right ht₁ hs.le
    nlinarith only [h, sq_nonneg s]
  have hLess : (t - 3 * s) * (Y : ℝ) ≤
      (d.totient : ℝ) * Real.log (Y : ℝ) * (Q.card : ℝ) - s * (Y : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hAstep hY
    nlinarith only [h, hQMass]
  have hBstep : t - ζ ≤ (1 - s) * (t - 3 * s) := by
    have h := mul_le_mul_of_nonneg_right (show t - 3 * s ≤ 1 by linarith only [ht₁, hs]) hs.le
    nlinarith only [h, hsζ]
  have hWeight : (t - ζ) * (Y : ℝ) ≤
      (d.totient : ℝ) * ∑ p ∈ Q, Real.log (p : ℝ) := by
    calc
      _ ≤ ((1 - s) * (t - 3 * s)) * (Y : ℝ) := mul_le_mul_of_nonneg_right hBstep hY
      _ = (1 - s) * ((t - 3 * s) * (Y : ℝ)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hLess (sub_nonneg.mpr hs1.le)).trans hQTrim
  rw [GoldbachColorAPEnum.weighted_class_eq_progression A hA d a hd ha hCo L] at hWeight
  exact hWeight
