import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CentralWeight
open Finset Filter
open scoped Topology

private def win (n : ℕ) := (range (n+1)).filter fun t => n ≤ 3*t ∧ 3*t ≤ 2*n ∧ t % 2 = 1
private noncomputable def w (p : ℕ) : ℝ := if p.Prime then Real.log (p:ℝ) else 0

private theorem card_win (n : ℕ) : 6*(win n).card ≤ n+12 := by
  let s := Finset.Icc (n/6) (n/3)
  have hcard : (win n).card ≤ s.card := by
    apply Finset.card_le_card_of_injOn (fun t => t/2)
    · intro t ht
      have hh := (mem_filter.mp ht).2
      change t / 2 ∈ Icc (n/6) (n/3)
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro t ht u hu h
      have ht' := (mem_filter.mp ht).2
      have hu' := (mem_filter.mp hu).2
      dsimp at h
      omega
  simp [s, Nat.card_Icc] at hcard
  omega

private theorem refl {n : ℕ} (hn : Even n) :
    (∑ t ∈ win n, w (n-t)) = ∑ t ∈ win n, w t := by
  have maps {t : ℕ} (ht : t ∈ win n) : n-t ∈ win n := by
    obtain ⟨q,hq⟩ := hn
    have h := mem_filter.mp ht
    have ht' := mem_range.mp h.1
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩
  have im : (win n).image (fun t => n-t) = win n := by
    ext t
    constructor
    · rintro ht
      obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
      exact maps hu
    · intro ht
      have h := mem_range.mp (mem_filter.mp ht).1
      exact mem_image.mpr ⟨n-t, maps ht, by omega⟩
  conv_rhs => rw [← im]
  rw [Finset.sum_image]
  intro t ht u hu h
  have ht' := mem_range.mp (mem_filter.mp ht).1
  have hu' := mem_range.mp (mem_filter.mp hu).1
  dsimp at h
  omega

private theorem sum_lb (n : ℕ) (hn : 9 ≤ n) :
    Chebyshev.theta (2*n/3 : ℕ) - Chebyshev.theta (n/3 : ℕ) ≤ ∑ t ∈ win n, w t := by
  have expand (x : ℕ) : Chebyshev.theta x = ∑ p ∈ Ioc 0 x, w p := by
    simp [Chebyshev.theta, w, sum_filter]
  have hs := Finset.sum_union (f := w) (Finset.Ioc_disjoint_Ioc_of_le
    (a := 0) (b := n/3) (c := n/3) (d := 2*n/3) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega)] at hs
  rw [expand, expand, hs, add_sub_cancel_left]
  let s := (Ioc (n/3) (2*n/3)).filter Nat.Prime
  have eq : (∑ p ∈ Ioc (n/3) (2*n/3), w p) = ∑ p ∈ s, w p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases h : p.Prime <;> simp [w,h]
  rw [eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have h := mem_filter.mp hp
    have hi := mem_Ioc.mp h.1
    obtain ⟨i,hi'⟩ := h.2.odd_of_ne_two (by omega)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩
  · intro t _ _
    unfold w
    split_ifs with ht
    · exact Real.log_nonneg (by exact_mod_cast ht.one_le)
    · rfl

private theorem theta_bounds {e : ℝ} (he : 0 < e) : ∃ K : ℕ, ∀ n ≥ K,
    (1-e)*n ≤ Chebyshev.theta n ∧ Chebyshev.theta n ≤ (1+e)*n := by
  have limN : Tendsto (fun n : ℕ ↦ Chebyshev.theta n / (n : ℝ)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [limN.eventually_const_lt (show 1-e < 1 by linarith),
    limN.eventually_lt_const (show 1 < 1+e by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hlo hhi hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨((lt_div_iff₀ hn').mp hlo).le, ((div_lt_iff₀ hn').mp hhi).le⟩

theorem proof : have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); ∀ (x2 : ℝ),   (0 : ℝ) < x2 →     ∃ (x4 : ℕ),       ∀ x5 ≥ x4,         have x7 : ℕ := (2 : ℕ) ^ x5;         have x8 : Finset ℕ := {x8 ∈ Finset.range (x7 + (1 : ℕ)) | x7 ≤ (3 : ℕ) * x8 ∧ (3 : ℕ) * x8 ≤ (2 : ℕ) * x7 ∧ x8 % (2 : ℕ) = (1 : ℕ)};         ((2 / 3 : ℝ) - x2) * ↑x7 ≤ ∑ x9 ∈ x8, ((2 : ℝ) * x1 x9 + (2 : ℝ) * x1 (x7 - x9) - (4 : ℝ)) := by
  intro weightDef e he
  obtain ⟨K,hK⟩ := theta_bounds (show 0 < e/32 by linarith)
  obtain ⟨J, hJ⟩ := exists_nat_ge (100/e)
  refine ⟨3*K+J+10, ?_⟩
  intro k hk
  let n : ℕ := 2^k
  have hkn : k ≤ n := k.lt_two_pow_self.le
  have hn : 9 ≤ n := by omega
  have evenN : Even n := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    exact ⟨2^j, by dsimp [n]; rw [pow_succ, mul_two]⟩
  have hnJ : (J:ℝ) ≤ n := by exact_mod_cast (show J ≤ n by omega)
  have hbudget := (div_le_iff₀ he).mp (hJ.trans hnJ)
  let a := n/3
  let b := 2*n/3
  have al : K ≤ a := by dsimp [a]; omega
  have bl : K ≤ b := by dsimp [b]; omega
  have hcard : 6*((win n).card:ℝ) ≤ (n:ℝ)+12 := by exact_mod_cast card_win n
  have hsum := sum_lb n hn
  change Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) ≤ _ at hsum
  have hl := (hK b bl).1
  have hu := (hK a al).2
  have h1 : (a:ℝ) + b ≤ n := by exact_mod_cast (show a+b ≤ n by dsimp [a,b]; omega)
  have h2 : 3*(b:ℝ) + 2 ≥ 2*n := by exact_mod_cast (show 3*b+2 ≥ 2*n by dsimp [b]; omega)
  have h3 : 3*(a:ℝ) ≤ n := by exact_mod_cast (show 3*a ≤ n by dsimp [a]; omega)
  have h4 := mul_le_mul_of_nonneg_left h1 he.le
  change (2/3-e)*(n:ℝ) ≤ ∑ t ∈ win n, (2*w t + 2*w (n-t) - 4)
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, refl evenN]
  simp only [sum_const, nsmul_eq_mul]
  linarith

end CentralWeight

theorem Conjectures.Cuts.Taska5d9337be66b43f28ebbbdf7 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); ∀ (x2 : ℝ),   (0 : ℝ) < x2 →     ∃ (x4 : ℕ),       ∀ x5 ≥ x4,         have x7 : ℕ := (2 : ℕ) ^ x5;         have x8 : Finset ℕ := {x8 ∈ Finset.range (x7 + (1 : ℕ)) | x7 ≤ (3 : ℕ) * x8 ∧ (3 : ℕ) * x8 ≤ (2 : ℕ) * x7 ∧ x8 % (2 : ℕ) = (1 : ℕ)};         ((2 / 3 : ℝ) - x2) * ↑x7 ≤ ∑ x9 ∈ x8, ((2 : ℝ) * x1 x9 + (2 : ℝ) * x1 (x7 - x9) - (4 : ℝ))) := by
  exact CentralWeight.proof
