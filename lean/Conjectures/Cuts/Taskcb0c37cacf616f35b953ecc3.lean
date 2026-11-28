import Mathlib

/-! Transfer lower prime-counting density to logarithmic mass in a fixed reduced class. -/

namespace DensityTransfer

open Finset Filter
open scoped Topology

def ap (q a X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun n => n.Prime ∧ n % q = a

/-- Relative lower counting density in one fixed reduced class implies the
same lower density for the logarithmic prime weight, normalized by φ(q). -/
theorem thetaLower (A : Set ℕ) [DecidablePred (fun n => n ∈ A)] (q a : ℕ) (t : ℝ)
    (hq : 2 ≤ q) (ha : a < q) (hc : a.Coprime q)
    (hd : ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ X ≥ T,
      (t-δ)*((ap q a X).card:ℝ) ≤ (((ap q a X).filter (fun n => n∈A)).card:ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ X ≥ T, (t-ε)*(X:ℝ) ≤
      (q.totient:ℝ)*(∑ n ∈ (ap q a X).filter (fun n => n∈A), Real.log n) := by
  classical
  let _ : NeZero q := ⟨by omega⟩
  let F (X : ℕ) := (ap q a X).filter (fun n => n ∈ A)
  let W (X : ℕ) := ∑ n ∈ F X, Real.log n
  let c := t-ε/2
  have ec (X : ℕ) :
      ((Ioc 0 X).filter fun n => n.Prime ∧ n ≡ a [MOD q]) = ap q a X := by
    ext n
    simp [ap, Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.succ_le_iff]
  have es (X : ℕ) :
      ((Ioc 0 X).filter fun n => n.Prime ∧ n % q=a ∧ n∈A) = F X := by
    ext n
    simp [F, ap, Nat.succ_le_iff, and_assoc]
  have hcnt : Tendsto (fun X : ℕ => ((ap q a X).card:ℝ)*Real.log X / X)
      atTop (𝓝 (q.totient:ℝ)⁻¹) := by
    have h := (Nat.tendsto_card_prime_modEq_mul_log_div_atTop hc).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Nat.floor_natCast, ec] using h
  have herr : Tendsto (fun X : ℕ => ((F X).card*Real.log X-W X)/(X:ℝ)) atTop (𝓝 0) := by
    have h := (Chebyshev.isLittleO_card_prime_with_mul_log_sum_prime_log_with
      (fun n => n % q=a ∧ n∈A)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Nat.floor_natCast, es, id_eq, W] using h
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have lim := (hcnt.const_mul (c*(q.totient:ℝ))).sub (herr.const_mul (q.totient:ℝ))
  have v : c*(q.totient:ℝ)*(q.totient:ℝ)⁻¹ - q.totient*0 = c := by
    rw [mul_zero, sub_zero, mul_assoc, mul_inv_cancel₀ hφ.ne', mul_one]
  rw [v] at lim
  have low := lim.eventually_const_lt (show t-ε < c by dsimp [c]; linarith)
  obtain ⟨T,hT⟩ := hd (ε/2) (by linarith)
  apply eventually_atTop.mp
  filter_upwards [low, eventually_ge_atTop T, eventually_ge_atTop 1] with X hlow hXT hX
  have hx : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hxlog : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hcX : c*((ap q a X).card:ℝ) ≤ ((F X).card:ℝ) := hT X hXT
  have hcomp := mul_le_mul_of_nonneg_right hcX hxlog
  change t-ε < c*(q.totient:ℝ)*(((ap q a X).card:ℝ)*Real.log X / X) -
    (q.totient:ℝ)*((((F X).card:ℝ)*Real.log X-W X)/(X:ℝ)) at hlow
  field_simp [hx.ne'] at hlow
  change (t-ε)*(X:ℝ) ≤ (q.totient:ℝ)*W X
  nlinarith only [hlow, mul_le_mul_of_nonneg_left hcomp hφ.le]

end DensityTransfer

namespace DensityTransfer
open Finset

/-- The reduced residue is nonzero, so the closed cutoff qL contributes
exactly the progression indices j < L, including the correct lower endpoint. -/
theorem sum_reindex (A : Set ℕ) [DecidablePred (· ∈ A)] (hA : ∀ n ∈ A, Nat.Prime n)
    (q a L : ℕ) (hq : 2 ≤ q) (ha : a < q) (hc : a.Coprime q) :
    (∑ n ∈ ((Icc 1 (q*L)).filter (fun n => n.Prime ∧ n % q = a)).filter (· ∈ A),
      Real.log (n:ℝ)) =
    ∑ j ∈ range L, if q*j+a ∈ A then Real.log ((q*j+a : ℕ):ℝ) else 0 := by
  classical
  have qp : 0 < q := by omega
  have ap : 0 < a := by
    by_contra! hz
    have h0 : a=0 := by omega
    simp [h0] at hc
    omega
  have recover (n : ℕ) (hn : n % q=a) : q*(n/q)+a=n := hn ▸ Nat.div_add_mod n q
  rw [← sum_filter]
  apply sum_bij' (fun n _ => n / q) (fun j _ => q*j+a)
  · intro n hn
    obtain ⟨hf,hnA⟩ := mem_filter.mp hn
    obtain ⟨hi,_,hr⟩ := mem_filter.mp hf
    have hle := (mem_Icc.mp hi).2
    have hlt : n < q*L := by
      apply lt_of_le_of_ne hle
      rintro rfl
      simp at hr
      omega
    exact mem_filter.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul qp).mpr (by simpa [Nat.mul_comm] using hlt)),
      (recover n hr).symm ▸ hnA⟩
  · intro j hj
    obtain ⟨hj,hA'⟩ := mem_filter.mp hj
    have hle : j+1 ≤ L := mem_range.mp hj
    have upper : q*j+a ≤ q*L := calc
      _ ≤ q*j+q := Nat.add_le_add_left ha.le _
      _ = q*(j+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hle
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,upper⟩,hA _ hA',
      by simpa only [Nat.mul_add_mod_self_left] using (Nat.mod_eq_of_lt ha)⟩,hA'⟩
  · intro n hn
    exact recover n (mem_filter.mp (mem_filter.mp hn).1).2.2
  · intro j _
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ qp, Nat.div_eq_of_lt ha, zero_add]
  · intro n hn
    rw [recover n (mem_filter.mp (mem_filter.mp hn).1).2.2]

end DensityTransfer

theorem Conjectures.Cuts.Taskcb0c37cacf616f35b953ecc3 : (∀ (x1 : Set ℕ) [x2 : DecidablePred fun (x2 : ℕ) => x2 ∈ x1],   (∀ x3 ∈ x1, Nat.Prime x3) →     ∀ (x4 x5 : ℕ) (x6 : ℝ),       (2 : ℕ) ≤ x4 →         x5 < x4 →           x5.Coprime x4 →             (0 : ℝ) ≤ x6 →               x6 ≤ (1 : ℝ) →                 have x12 : ℕ → Finset ℕ := fun (x12 : ℕ) => {x13 ∈ Finset.Icc (1 : ℕ) x12 | Nat.Prime x13 ∧ x13 % x4 = x5};                 (∀ (x13 : ℝ), (0 : ℝ) < x13 → ∃ (x15 : ℕ), ∀ x16 ≥ x15, (x6 - x13) * ↑(x12 x16).card ≤ ↑{x18 ∈ x12 x16 | x18 ∈ x1}.card) → ∀ (x14 : ℝ), (0 : ℝ) < x14 → ∃ (x16 : ℕ), ∀ x17 ≥ x16, (x6 - x14) * ↑(x4 * x17) ≤ ↑x4.totient * ∑ x19 ∈ Finset.range x17, if x4 * x19 + x5 ∈ x1 then Real.log ↑(x4 * x19 + x5) else (0 : ℝ)) := by
  intro A inst hA q a t hq ha hc _ht _ht1 primes hd ε hε
  obtain ⟨T,hT⟩ := DensityTransfer.thetaLower A q a t hq ha hc hd ε hε
  refine ⟨T, ?_⟩
  intro L hL
  have hx : T ≤ q * L := hL.trans (Nat.le_mul_of_pos_left L (by omega))
  have h := hT (q*L) hx
  unfold DensityTransfer.ap at h
  rwa [DensityTransfer.sum_reindex A hA q a L hq ha hc] at h
