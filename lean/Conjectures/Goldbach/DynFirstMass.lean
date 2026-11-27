import Mathlib

open Finset Filter
open scoped Topology

namespace DynFirstMassProof

private noncomputable def block (base : ℕ) : Finset ℕ :=
  (⌊(3 / 2 : ℝ) * base⌋₊).primesLE \ base.primesLE

private theorem block_spec {base prime : ℕ} (h : prime ∈ block base) :
    prime.Prime ∧ base < prime ∧ 2 * prime ≤ 3 * base := by
  obtain ⟨upper, lower⟩ := mem_sdiff.mp h
  obtain ⟨bound, primality⟩ := Nat.mem_primesLE.mp upper
  have hreal := (Nat.le_floor_iff (by positivity : 0 ≤ (3 / 2 : ℝ) * base)).mp bound
  refine ⟨primality, lt_of_not_ge (fun hle => lower (Nat.mem_primesLE.mpr ⟨hle, primality⟩)), ?_⟩
  exact_mod_cast (show 2 * (prime : ℝ) ≤ 3 * base by linarith)

private theorem block_mass : ∀ᶠ base : ℕ in atTop,
    (base : ℝ) ≤ 16 * ((block base).card : ℝ) * Real.log base := by
  have natTop := (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaledTop : Tendsto (fun base : ℕ => (3 / 2 : ℝ) * base) atTop atTop :=
    natTop.const_mul_atTop (by norm_num)
  have lower := (Chebyshev.tendsto_theta_div_atTop.comp scaledTop).eventually_const_lt
    (show (7/8 : ℝ) < 1 by norm_num)
  have upper := (Chebyshev.tendsto_theta_div_atTop.comp natTop).eventually_lt_const
    (show (1 : ℝ) < 9/8 by norm_num)
  filter_upwards [lower, upper, eventually_ge_atTop 2] with base hlo hhi hbase
  have hb : (2 : ℝ) ≤ base := by exact_mod_cast hbase
  have hlo' : 7/8 * ((3/2 : ℝ)*base) < Chebyshev.theta ((3/2 : ℝ)*base) :=
    (lt_div_iff₀ (by positivity)).mp hlo
  have hhi' : Chebyshev.theta base < 9/8 * base := (div_lt_iff₀ (by positivity)).mp hhi
  have sub := Nat.primesLE_mono (Nat.le_floor (show (base : ℝ) ≤ 3/2 * base by linarith))
  have hsum : (∑ prime ∈ block base, Real.log prime) + Chebyshev.theta base =
      Chebyshev.theta ((3/2 : ℝ) * base) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE, block,
      Finset.sum_sdiff sub]
  have hbound : (∑ prime ∈ block base, Real.log prime) ≤
      ((block base).card : ℝ) * (2 * Real.log base) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro prime hp
    obtain ⟨hprime, _, hcap⟩ := block_spec hp
    have hcap' : 2 * (prime : ℝ) ≤ 3 * base := by exact_mod_cast hcap
    have hle : (prime : ℝ) ≤ (base : ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show (0 : ℝ) ≤ base by positivity)]
    simpa [Real.log_pow] using Real.log_le_log (by exact_mod_cast hprime.pos) hle
  linarith

private theorem rectangle (scale : ℕ) (hs : 4 ≤ scale.sqrt) :
    (block scale.sqrt).card * (block scale).card ≤
      ∑ target ∈ (Icc scale (2*scale)).filter (fun n => Even n),
        (((Icc scale.sqrt (2*scale.sqrt)).filter Nat.Prime).filter
          (fun prime => prime ≤ target ∧ Nat.Prime (target-prime))).card := by
  classical
  rw [← card_product, ← card_sigma]
  apply card_le_card_of_injOn (fun pair : ℕ × ℕ => (⟨pair.1 + pair.2, pair.1⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨first, second⟩ hpair
    obtain ⟨hf, hfb, hfc⟩ := block_spec (mem_product.mp hpair).1
    obtain ⟨hsnd, hsb, hsc⟩ := block_spec (mem_product.mp hpair).2
    have hsmall : 4 * scale.sqrt ≤ scale := by
      calc 4 * scale.sqrt ≤ scale.sqrt * scale.sqrt := Nat.mul_le_mul_right _ hs
           _ ≤ scale := Nat.sqrt_le _
    have heven := (hf.odd_of_ne_two (by omega)).add_odd (hsnd.odd_of_ne_two (by omega))
    apply Finset.mem_sigma.mpr
    simp only [mem_filter, mem_Icc, Nat.add_sub_cancel_left]
    exact ⟨⟨⟨by omega, by omega⟩, heven⟩, ⟨⟨by omega, by omega⟩, hf⟩, by omega, hsnd⟩
  · rintro ⟨first, second⟩ _ ⟨other, last⟩ _ heq
    have hfirst : first = other := congrArg (fun pair : Σ _ : ℕ, ℕ => pair.2) heq
    have hsum : first + second = other + last := congrArg Sigma.fst heq
    exact Prod.ext hfirst (by omega)

theorem _root_.Conjectures.Goldbach.DynFirstMass : let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, c*(X:ℝ)*M X ≤ ∑ n ∈ E X, (H X n:ℝ) := by
  dsimp only
  obtain ⟨threshold, hmass⟩ := eventually_atTop.1 block_mass
  refine ⟨1/512, by norm_num, (max threshold 4)^2, ?_⟩
  intro scale hscale
  have hroot := Nat.le_sqrt'.2 hscale
  have hfour : 4 ≤ scale.sqrt := le_trans (le_max_right ..) hroot
  have hthreshold : threshold ≤ scale.sqrt := le_trans (le_max_left ..) hroot
  have hle := Nat.sqrt_le_self scale
  have hshort := hmass _ hthreshold
  have hlong := hmass _ (hthreshold.trans hle)
  have hlog : 0 < Real.log (scale : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < scale by omega))
  have hlogmono : Real.log (scale.sqrt : ℝ) ≤ Real.log (scale : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < scale.sqrt by omega)) (by exact_mod_cast hle)
  have hlift : Real.sqrt (scale : ℝ) ≤ 2 * (scale.sqrt : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hs : (scale : ℝ) < ((scale.sqrt : ℝ) + 1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' scale
      have hf : (4 : ℝ) ≤ scale.sqrt := by exact_mod_cast hfour
      nlinarith [sq_nonneg ((scale.sqrt : ℝ) - 1)]
  have shortBound : Real.sqrt (scale : ℝ) ≤ 32 * ((block scale.sqrt).card : ℝ) * Real.log scale := by
    have := mul_le_mul_of_nonneg_left hlogmono (by positivity : 0 ≤ 16 * ((block scale.sqrt).card : ℝ))
    linarith
  have bound := mul_le_mul hlong shortBound (Real.sqrt_nonneg _) (by positivity)
  calc
    _ ≤ ((block scale.sqrt).card : ℝ) * ((block scale).card : ℝ) := by
      rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hlog)]
      linarith only [bound]
    _ ≤ _ := by exact_mod_cast rectangle scale hfour

end DynFirstMassProof
