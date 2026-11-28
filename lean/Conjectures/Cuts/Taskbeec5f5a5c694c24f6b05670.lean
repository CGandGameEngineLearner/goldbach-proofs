import Mathlib

/-!
# First moment for the six-power Linnik–Goldbach decomposition

This is the unconditional first-moment input to the finite signed-reflection
argument of Li and Liu, https://arxiv.org/html/2610.15784v1#S2 (8)–(13).
The proof uses the prime number theorem in the pinned Mathlib. Uniformity in
the lower prime cutoff and exponent cap follows by retaining one common prime
interval for every shifted triple. The upper bounds for the one- and two-power
terms need only the full Chebyshev sum. For another application of the same
Mathlib PNT in this project see Conjectures/Goldbach/DynFirstMass.lean.
-/

namespace LinnikFirstInput

open Filter
open scoped Topology BigOperators

/-- For large K the same interval of odd primes works for every admissible shift.
The missing endpoints and the lower cutoff together occupy O(K/10^6). -/
theorem theta_window_uniform : ∃ T : ℕ, ∀ K ≥ T,
    let B := K / 1000000
    let U := 2*K - B - 1
    2 ≤ B ∧ B ≤ U ∧
    (9999 / 10000 : ℝ) * (2 * (K:ℝ)) ≤
      Chebyshev.theta (U:ℝ) - Chebyshev.theta (B:ℝ) ∧
    Chebyshev.theta (2*K : ℕ) ≤ (10001 / 10000 : ℝ) * (2*(K:ℝ)) := by
  have hlim : Tendsto (fun n : ℕ => Chebyshev.theta n / (n:ℝ)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ≥ M,
      (99999/100000:ℝ)*n < Chebyshev.theta n ∧
      Chebyshev.theta n < (100001/100000:ℝ)*n := by
    apply Filter.eventually_atTop.mp
    filter_upwards [hlim.eventually_const_lt (show (99999/100000:ℝ)<1 by norm_num),
      hlim.eventually_lt_const (show (1:ℝ)<100001/100000 by norm_num), eventually_ge_atTop (1:ℕ)]
      with n hl hu hn
    have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact ⟨(lt_div_iff₀ hn').mp hl,(div_lt_iff₀ hn').mp hu⟩
  refine ⟨1000000*(M+3), ?_⟩
  intro K hK
  dsimp only
  let B := K / 1000000
  let U := 2*K - B - 1
  have hB : M ≤ B := by dsimp [B]; omega
  have hB' : 2 ≤ B := by dsimp [B]; omega
  have hcap : B*1000000 ≤ K := Nat.div_mul_le_self _ _
  have hU : B ≤ U := by dsimp [U]; omega
  have hnat : U+B+1 = 2*K := by dsimp [U]; omega
  have hreal : (U:ℝ)+(B:ℝ)+1 = 2*(K:ℝ) := by exact_mod_cast hnat
  have hsmall : (B:ℝ)*1000000 ≤ K := by exact_mod_cast hcap
  have hKmin : (3000000:ℝ) ≤ K := by exact_mod_cast (show 3000000 ≤ K by omega)
  have hl := (hM U (le_trans hB hU)).1
  have hb := (hM B hB).2
  have hh := (hM (2*K) (by omega)).2
  push_cast at hh ⊢
  refine ⟨hB', hU, ?_, ?_⟩
  · change (9999/10000:ℝ)*(2*(K:ℝ)) ≤ Chebyshev.theta (U:ℝ) - Chebyshev.theta (B:ℝ)
    linarith
  · linarith

end LinnikFirstInput
namespace LinnikSix

/-- The positive exponents in an ordered tuple are written as `a i + 1`. -/
def dyadicShift {j L : ℕ} (a : Fin j → Fin L) : ℕ :=
  ∑ i, 2 ^ ((a i).val + 1)

/-- Li–Liu, arXiv:2610.15784v1, (8), on a target at most the outer parameter N.
The integer cutoff is the floor of the lower prime cutoff. -/
noncomputable def primePowerWeight (j L cutoff x : ℕ) : ℝ :=
  ∑ a : Fin j → Fin L,
    let p := x - dyadicShift a
    if cutoff < p ∧ p.Prime then Real.log p else 0

noncomputable def signedWeight (L cutoff : ℕ) {K : ℕ} (i : Fin K) : ℝ :=
  primePowerWeight 3 L cutoff (2*i.val+1) -
    (L : ℝ) / 4 * primePowerWeight 2 L cutoff (2*i.val+1) -
    (L : ℝ)^2 / 16 * primePowerWeight 1 L cutoff (2*i.val+1)


end LinnikSix



namespace LinnikFirstInput

open Finset

noncomputable def clippedWeight (B p : ℕ) : ℝ :=
  if B < p ∧ p.Prime then Real.log p else 0

private theorem clippedWeight_nonnegative (B p : ℕ) : 0 ≤ clippedWeight B p := by
  unfold clippedWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.2.one_le)
  · exact le_rfl

/-- Positive odd targets indexed by Fin K include every odd prime in the indicated interval,
after the same even translation. The cutoff 2 on the left removes the even prime. -/
theorem fixedShift_lower (K B B0 U t : ℕ) (he : Even t) (hB : B ≤ B0) (h2 : 2 ≤ B0)
    (hBU : B0 ≤ U) (hU : U+t < 2*K) :
    Chebyshev.theta (U : ℝ) - Chebyshev.theta (B0 : ℝ) ≤
      ∑ i : Fin K, clippedWeight B (2*i.val+1-t) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => clippedWeight B (2*i+1-t)) K,
    Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  let S := U.primesLE \ B0.primesLE
  have hs : ∑ p ∈ S, Real.log (p : ℝ) =
      (∑ p ∈ U.primesLE, Real.log (p : ℝ)) - ∑ p ∈ B0.primesLE, Real.log (p : ℝ) := by
    apply eq_sub_iff_add_eq.mpr
    exact Finset.sum_sdiff (Nat.primesLE_mono hBU)
  rw [← hs]
  have facts (p : ℕ) (hp : p ∈ S) : B0 < p ∧ p ≤ U ∧ p.Prime ∧ Odd (p+t) := by
    obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hle, hpr⟩ := Nat.mem_primesLE.mp hmem
    have hlt : B0 < p := by
      by_contra! hle
      exact hnot (Nat.mem_primesLE.mpr ⟨hle, hpr⟩)
    exact ⟨hlt, hle, hpr, (hpr.odd_of_ne_two (by omega)).add_even he⟩
  apply Finset.sum_le_sum_of_injOn (fun p => (p+t)/2)
  · intro p hp q hq hpq
    obtain ⟨_, _, _, a, ha⟩ := facts p hp
    obtain ⟨_, _, _, b, hb⟩ := facts q hq
    change (p+t)/2 = (q+t)/2 at hpq
    omega
  · intro i hi
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
    obtain ⟨_, hle, _, _⟩ := facts p hp
    exact mem_range.mpr (by omega)
  · intro p hp
    obtain ⟨hlt, _, hpr, a, ha⟩ := facts p hp
    have hsub : 2*((p+t)/2)+1-t=p := by omega
    simp [hsub, clippedWeight, lt_of_le_of_lt hB hlt, hpr]
  · intro i _ _
    exact clippedWeight_nonnegative _ _

/-- Each nonzero summand comes from a distinct prime below 2K. -/
theorem fixedShift_upper (K B t : ℕ) :
    (∑ i : Fin K, clippedWeight B (2*i.val+1-t)) ≤ Chebyshev.theta (2*K : ℕ) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => clippedWeight B (2*i+1-t)) K,
    Chebyshev.theta_eq_sum_primesLE_log]
  let p := fun i : ℕ => 2*i+1-t
  let S := (range K).filter (fun i => B < p i ∧ (p i).Prime)
  have hS : (∑ i ∈ range K, clippedWeight B (p i)) = ∑ i ∈ S, Real.log (p i : ℝ) := by
    simp only [S, sum_filter, clippedWeight]
  change (∑ i ∈ range K, clippedWeight B (p i)) ≤ _
  rw [hS]
  apply Finset.sum_le_sum_of_injOn p
  · intro i hi j hj hij
    obtain ⟨hi₀, _⟩ := (mem_filter.mp hi).2
    obtain ⟨hj₀, _⟩ := (mem_filter.mp hj).2
    dsimp [p] at hi₀ hj₀ hij
    omega
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
    obtain ⟨hiK, _, hiP⟩ := mem_filter.mp hi
    refine Nat.mem_primesLE.mpr ⟨?_, hiP⟩
    have := mem_range.mp hiK
    dsimp [p]
    omega
  · intro i hi
    exact le_rfl
  · intro q hq _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_le)

end LinnikFirstInput

namespace LinnikFirstInput

open Finset

private lemma shifted_mass (j K L B : ℕ) :
    (∑ i : Fin K, LinnikSix.primePowerWeight j L B (2*i.val+1)) =
      ∑ a : Fin j → Fin L, ∑ i : Fin K,
        clippedWeight B (2*i.val+1-LinnikSix.dyadicShift a) := by
  unfold LinnikSix.primePowerWeight clippedWeight
  exact Finset.sum_comm

private lemma shiftEven {j L : ℕ} (a : Fin j → Fin L) : Even (LinnikSix.dyadicShift a) := by
  refine ⟨∑ i, 2^(a i).val, ?_⟩
  unfold LinnikSix.dyadicShift
  simp only [pow_succ]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by omega)

private lemma shiftBound {j L : ℕ} (a : Fin j → Fin L) :
    LinnikSix.dyadicShift a ≤ j * 2^L := by
  unfold LinnikSix.dyadicShift
  calc
    _ ≤ ∑ _i : Fin j, 2^L := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.pow_le_pow_right (by omega) (a i).isLt
    _ = _ := by simp

theorem signed_mass_of_fixed_bounds
    (lower : ∀ K B B0 U t : ℕ, Even t → B ≤ B0 → 2 ≤ B0 → B0 ≤ U → U+t < 2*K →
      Chebyshev.theta (U:ℝ) - Chebyshev.theta (B0:ℝ) ≤
        ∑ i : Fin K, clippedWeight B (2*i.val+1-t))
    (upper : ∀ K B t : ℕ, (∑ i : Fin K, clippedWeight B (2*i.val+1-t)) ≤
      Chebyshev.theta (2*K : ℕ)) :
    ∃ T : ℕ, ∀ K L cutoff : ℕ, T ≤ K → 0 < L → cutoff + 3 * 2 ^ L ≤ K / 1000000 →
      ((11:ℝ)/16 - 1/4096) * (2*(K:ℝ)) * (L:ℝ)^3 ≤
        ∑ i : Fin K, LinnikSix.signedWeight L cutoff i := by
  classical
  obtain ⟨T,hT⟩ := theta_window_uniform
  refine ⟨max T 2, ?_⟩
  intro K L B hK hL hsmall
  let B0 := K/1000000
  let U := 2*K - B0 - 1
  obtain ⟨h2,hBU,hθlo,hθup⟩ := hT K (le_trans (le_max_left _ _) hK)
  have hB : B ≤ B0 := by dsimp [B0]; omega
  have hlargeK : 2 ≤ K := le_trans (le_max_right _ _) hK
  have hBK : B0 ≤ K := Nat.div_le_self _ _
  let r (j : ℕ) : ℝ := ∑ i : Fin K, LinnikSix.primePowerWeight j L B (2*i.val+1)
  have massU (j : ℕ) : r j ≤ (L:ℝ)^j * ((10001/10000:ℝ)*(2*(K:ℝ))) := by
    dsimp [r]
    rw [shifted_mass]
    calc
      _ ≤ ∑ _a : Fin j → Fin L, ((10001/10000:ℝ)*(2*(K:ℝ))) := by
        exact Finset.sum_le_sum fun a _ => (upper K B (LinnikSix.dyadicShift a)).trans hθup
      _ = _ := by simp
  have mass3 : (L:ℝ)^3 * ((9999/10000:ℝ)*(2*(K:ℝ))) ≤ r 3 := by
    dsimp [r]
    rw [shifted_mass]
    calc
      _ = ∑ _a : Fin 3 → Fin L, ((9999/10000:ℝ)*(2*(K:ℝ))) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a _
        have hlt : U + LinnikSix.dyadicShift a < 2*K := by
          have hb := shiftBound a
          change B + 3*2^L ≤ B0 at hsmall
          dsimp [U]; omega
        exact hθlo.trans (lower K B B0 U _ (shiftEven a) hB h2 hBU hlt)
  change _ ≤ ∑ i : Fin K, (_ - _ - _)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change _ ≤ r 3 - (L:ℝ) / 4 * r 2 - (L:ℝ)^2 / 16 * r 1
  have h₂ := mul_le_mul_of_nonneg_left (massU 2) (show 0 ≤ (L:ℝ)/4 by positivity)
  have h₁ := mul_le_mul_of_nonneg_left (massU 1) (show 0 ≤ (L:ℝ)^2/16 by positivity)
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) K) (pow_nonneg (Nat.cast_nonneg (α:=ℝ) L) 3)]

end LinnikFirstInput
namespace LinnikFirstInput

theorem first_mass_unconditional :
    ∃ T : ℕ, ∀ K L cutoff : ℕ, T ≤ K → 0 < L → cutoff + 3 * 2 ^ L ≤ K / 1000000 →
      ((11:ℝ)/16 - 1/4096) * (2*(K:ℝ)) * (L:ℝ)^3 ≤
        ∑ i : Fin K, LinnikSix.signedWeight L cutoff i :=
  signed_mass_of_fixed_bounds fixedShift_lower fixedShift_upper

end LinnikFirstInput

/-- The exact first child of the registered-style decomposition. -/
theorem Conjectures.Cuts.Taskbeec5f5a5c694c24f6b05670 :
    ∃ T : ℕ, ∀ K L cutoff : ℕ, T ≤ K → 0 < L →
      cutoff + 3 * 2^L ≤ K / 1000000 →
      let w := fun (j x : ℕ) => ∑ a : Fin j → Fin L,
        let p := x - ∑ i : Fin j, 2 ^ ((a i).val + 1)
        if cutoff < p ∧ p.Prime then Real.log p else 0
      let f := fun (i : Fin K) =>
        let x := 2*i.val+1
        w 3 x - (L : ℝ)/4 * w 2 x - (L : ℝ)^2/16 * w 1 x
      ((11 : ℝ)/16 - 1/4096) * (2*(K : ℝ)) * (L : ℝ)^3 ≤ ∑ i : Fin K, f i :=
  LinnikFirstInput.first_mass_unconditional
