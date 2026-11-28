import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace M0Finite
open Finset

def approx (q : ℚ) : ℚ :=
  2 * ∑ i ∈ Finset.range 15, ((q-1)/(q+1))^(2*i+1) / (2*(i:ℚ)+1)

theorem log_bounds (q : ℚ) (hq : 1 ≤ q) (h2 : q ≤ 2) :
    (approx q : ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (approx q:ℝ) + 1/1000000000000 := by
  let x := ((q:ℝ)-1)/(q+1)
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have h2' : (q:ℝ) ≤ 2 := by exact_mod_cast h2
  have hp : (0:ℝ) < q+1 := by linarith
  have hx : 0 ≤ x := div_nonneg (by linarith) hp.le
  have hx3 : x ≤ 1/3 := (div_le_iff₀ hp).2 (by linarith)
  have hx1 : x < 1 := by linarith
  have hid : (1+x)/(1-x) = q := by
    apply (div_eq_iff (by linarith : 1-x ≠ 0)).2
    dsimp [x]
    field_simp
    ring
  have hlo := Real.sum_range_le_log_div hx hx1 15
  have hhi := Real.log_div_le_sum_range_add hx hx1 15
  rw [hid] at hlo hhi
  have hv : (approx q : ℝ) = 2 * ∑ i ∈ range 15, x ^ (2*i+1) / (2*(i:ℝ)+1) := by
    unfold approx
    push_cast
    rfl
  rw [hv]
  constructor
  · linarith
  · have hs := pow_le_pow_left₀ hx hx3 2
    have hh := pow_le_pow_left₀ hx hx3 31
    have err : x^31 / (1-x^2) ≤ 1/2000000000000 := by
      apply (div_le_iff₀ (by norm_num at hs; linarith)).2
      norm_num at hh hs
      linarith
    norm_num only at hhi
    linarith

noncomputable def term (p : ℕ) : ℝ :=
  Real.log (1 - 1/(p:ℝ)) + 1/(p:ℝ) - Real.log (1 - 1/(p:ℝ)^2)/2 -
    Real.log (1 - 1/(p:ℝ)^3)/3

def quotR (n : ℕ) : ℚ := (n:ℚ)/(n-1)

theorem neglog (n : ℕ) (hn : 2 ≤ n) :
    -(approx (quotR n):ℝ) - 1/1000000000000 ≤ Real.log (1 - 1/(n:ℝ)) ∧
    Real.log (1 - 1/(n:ℝ)) ≤ -(approx (quotR n):ℝ) := by
  have hn' : (2:ℚ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n:ℚ)-1 := by linarith
  obtain ⟨hlo,hhi⟩ := log_bounds (quotR n) ((le_div_iff₀ hp).2 (by linarith))
    ((div_le_iff₀ hp).2 (by linarith))
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have eq : 1-1/(n:ℝ) = ((quotR n:ℚ):ℝ)⁻¹ := by
    unfold quotR
    push_cast
    rw [inv_div]
    field_simp
  rw [eq, Real.log_inv]
  constructor <;> linarith

def termApprox (p : ℕ) : ℚ := -(approx (quotR p)) + 1/(p:ℚ) +
  approx (quotR (p^2))/2 + approx (quotR (p^3))/3

theorem term_bounds (p : ℕ) (hp : 2 ≤ p) :
    (termApprox p:ℝ) - 2/1000000000000 ≤ term p ∧
    term p ≤ (termApprox p:ℝ) + 2/1000000000000 := by
  have h1 := neglog p hp
  have hp1 : p ≤ p^2 := Nat.le_self_pow (by decide) _
  have hp2 : p ≤ p^3 := Nat.le_self_pow (by decide) _
  have h2 := neglog (p^2) (hp.trans hp1)
  have h3 := neglog (p^3) (hp.trans hp2)
  push_cast at h2 h3
  unfold termApprox term
  push_cast
  constructor <;> linarith


private theorem bound_transfer (p : ℕ) (l u : ℤ) (hp : 2 ≤ p)
    (hl : (l:ℚ)/1000000000000 ≤ termApprox p - 2/1000000000000)
    (hu : termApprox p + 2/1000000000000 ≤ (u:ℚ)/1000000000000) :
    (l:ℝ)/1000000000000 ≤ term p ∧ term p ≤ (u:ℝ)/1000000000000 := by
  constructor
  · refine le_trans ?_ (term_bounds p hp).1
    have h := (Rat.cast_le (K := ℝ)).mpr hl
    push_cast at h
    exact h
  · refine le_trans (term_bounds p hp).2 ?_
    have h := (Rat.cast_le (K := ℝ)).mpr hu
    push_cast at h
    exact h

private theorem cert2 : (-4795680129:ℝ)/1000000000000 ≤ term 2 ∧ term 2 ≤ (-4795680122:ℝ)/1000000000000 :=
  bound_transfer 2 (-4795680129) (-4795680122) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert3 : (-660147623:ℝ)/1000000000000 ≤ term 3 ∧ term 3 ≤ (-660147616:ℝ)/1000000000000 :=
  bound_transfer 3 (-660147623) (-660147616) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert5 : (-55163492:ℝ)/1000000000000 ≤ term 5 ∧ term 5 ≤ (-55163485:ℝ)/1000000000000 :=
  bound_transfer 5 (-55163492) (-55163485) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert7 : (-10656671:ℝ)/1000000000000 ≤ term 7 ∧ term 7 ≤ (-10656664:ℝ)/1000000000000 :=
  bound_transfer 7 (-10656671) (-10656664) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert11 : (-1155098:ℝ)/1000000000000 ≤ term 11 ∧ term 11 ≤ (-1155091:ℝ)/1000000000000 :=
  bound_transfer 11 (-1155098) (-1155091) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert13 : (-506409:ℝ)/1000000000000 ≤ term 13 ∧ term 13 ≤ (-506402:ℝ)/1000000000000 :=
  bound_transfer 13 (-506409) (-506402) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert17 : (-134306:ℝ)/1000000000000 ≤ term 17 ∧ term 17 ≤ (-134299:ℝ)/1000000000000 :=
  bound_transfer 17 (-134306) (-134299) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert19 : (-77393:ℝ)/1000000000000 ≤ term 19 ∧ term 19 ≤ (-77386:ℝ)/1000000000000 :=
  bound_transfer 19 (-77393) (-77386) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert23 : (-29993:ℝ)/1000000000000 ≤ term 23 ∧ term 23 ≤ (-29986:ℝ)/1000000000000 :=
  bound_transfer 23 (-29993) (-29986) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert29 : (-9482:ℝ)/1000000000000 ≤ term 29 ∧ term 29 ≤ (-9475:ℝ)/1000000000000 :=
  bound_transfer 29 (-9482) (-9475) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert31 : (-6807:ℝ)/1000000000000 ≤ term 31 ∧ term 31 ≤ (-6800:ℝ)/1000000000000 :=
  bound_transfer 31 (-6807) (-6800) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert37 : (-2824:ℝ)/1000000000000 ≤ term 37 ∧ term 37 ≤ (-2817:ℝ)/1000000000000 :=
  bound_transfer 37 (-2824) (-2817) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert41 : (-1695:ℝ)/1000000000000 ≤ term 41 ∧ term 41 ≤ (-1688:ℝ)/1000000000000 :=
  bound_transfer 41 (-1695) (-1688) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert43 : (-1338:ℝ)/1000000000000 ≤ term 43 ∧ term 43 ≤ (-1331:ℝ)/1000000000000 :=
  bound_transfer 43 (-1338) (-1331) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert47 : (-860:ℝ)/1000000000000 ≤ term 47 ∧ term 47 ≤ (-853:ℝ)/1000000000000 :=
  bound_transfer 47 (-860) (-853) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert53 : (-474:ℝ)/1000000000000 ≤ term 53 ∧ term 53 ≤ (-467:ℝ)/1000000000000 :=
  bound_transfer 53 (-474) (-467) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert59 : (-279:ℝ)/1000000000000 ≤ term 59 ∧ term 59 ≤ (-272:ℝ)/1000000000000 :=
  bound_transfer 59 (-279) (-272) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert61 : (-237:ℝ)/1000000000000 ≤ term 61 ∧ term 61 ≤ (-230:ℝ)/1000000000000 :=
  bound_transfer 61 (-237) (-230) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert67 : (-150:ℝ)/1000000000000 ≤ term 67 ∧ term 67 ≤ (-143:ℝ)/1000000000000 :=
  bound_transfer 67 (-150) (-143) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert71 : (-113:ℝ)/1000000000000 ≤ term 71 ∧ term 71 ≤ (-106:ℝ)/1000000000000 :=
  bound_transfer 71 (-113) (-106) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert73 : (-99:ℝ)/1000000000000 ≤ term 73 ∧ term 73 ≤ (-92:ℝ)/1000000000000 :=
  bound_transfer 73 (-99) (-92) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert79 : (-68:ℝ)/1000000000000 ≤ term 79 ∧ term 79 ≤ (-61:ℝ)/1000000000000 :=
  bound_transfer 79 (-68) (-61) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert83 : (-54:ℝ)/1000000000000 ≤ term 83 ∧ term 83 ≤ (-47:ℝ)/1000000000000 :=
  bound_transfer 83 (-54) (-47) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert89 : (-39:ℝ)/1000000000000 ≤ term 89 ∧ term 89 ≤ (-32:ℝ)/1000000000000 :=
  bound_transfer 89 (-39) (-32) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert97 : (-27:ℝ)/1000000000000 ≤ term 97 ∧ term 97 ≤ (-20:ℝ)/1000000000000 :=
  bound_transfer 97 (-27) (-20) (by decide) (by decide +kernel) (by decide +kernel)

private theorem piLog : (49770030245:ℝ)/100000000000 ≤ Real.log (Real.pi^2/6) ∧
    Real.log (Real.pi^2/6) ≤ (49770030249:ℝ)/100000000000 := by
  let a : ℚ := 164493406683/100000000000
  let b : ℚ := 164493406686/100000000000
  have ha : (a:ℝ) ≤ Real.pi^2/6 := by
    have h := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2
    norm_num [a] at *
    linarith
  have hb : Real.pi^2/6 ≤ (b:ℝ) := by
    have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d20.le 2
    norm_num [b] at *
    linarith
  have hla := (log_bounds a (by norm_num [a]) (by norm_num [a])).1
  have hlb := (log_bounds b (by norm_num [b]) (by norm_num [b])).2
  have h1 : (49770030245:ℚ)/100000000000 ≤ approx a := by decide +kernel
  have h2 : approx b + 1/1000000000000 ≤ (49770030249:ℚ)/100000000000 := by decide +kernel
  constructor
  · apply le_trans _ (Real.log_le_log (by norm_num [a]) ha)
    have h := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at h
    exact h.trans hla
  · apply le_trans (Real.log_le_log (by positivity) hb)
    have h := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at h
    exact hlb.trans h

theorem proof : have x1 : ℕ → ℝ := fun (x1 : ℕ) => Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ)) + (1 : ℝ) / (↑x1 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ) ^ (2 : ℕ)) / (2 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ) ^ (3 : ℕ)) / (3 : ℝ); have x2 : ℝ := -(Real.log (Real.pi ^ (2 : ℕ) / (6 : ℝ)) / (2 : ℝ)) + ∑ x2 ∈ Finset.range (101 : ℕ) with Nat.Prime x2, x1 x2; -0.25437377 ≤ x2 ∧ x2 ≤ -0.25437368 := by
  let val := -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (Finset.range 101).filter Nat.Prime, term p
  change -0.25437377 ≤ val ∧ val ≤ -0.25437368
  have heq : ((Finset.range 101).filter Nat.Prime) = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} := by decide +kernel
  dsimp only [val]
  rw [heq]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, or_false, false_or, not_false_eq_true]
  constructor
  · linarith only [piLog.2, cert2.1, cert3.1, cert5.1, cert7.1, cert11.1, cert13.1, cert17.1, cert19.1, cert23.1, cert29.1, cert31.1, cert37.1, cert41.1, cert43.1, cert47.1, cert53.1, cert59.1, cert61.1, cert67.1, cert71.1, cert73.1, cert79.1, cert83.1, cert89.1, cert97.1]
  · linarith only [piLog.1, cert2.2, cert3.2, cert5.2, cert7.2, cert11.2, cert13.2, cert17.2, cert19.2, cert23.2, cert29.2, cert31.2, cert37.2, cert41.2, cert43.2, cert47.2, cert53.2, cert59.2, cert61.2, cert67.2, cert71.2, cert73.2, cert79.2, cert83.2, cert89.2, cert97.2]
end M0Finite

theorem Conjectures.Cuts.Tasked4086932a43867e5cb19d77 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ)) + (1 : ℝ) / (↑x1 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ) ^ (2 : ℕ)) / (2 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ) ^ (3 : ℕ)) / (3 : ℝ); have x2 : ℝ := -(Real.log (Real.pi ^ (2 : ℕ) / (6 : ℝ)) / (2 : ℝ)) + ∑ x2 ∈ Finset.range (101 : ℕ) with Nat.Prime x2, x1 x2; -0.25437377 ≤ x2 ∧ x2 ≤ -0.25437368) := by
  exact M0Finite.proof
