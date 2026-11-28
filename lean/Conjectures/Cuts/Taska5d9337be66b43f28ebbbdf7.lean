import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The linear term involves only one prime weight at a time. Reflection permutes
the odd central window, so the two weighted sums agree. The prime number
theorem estimates their common mass, and counting odd indices controls the
constant subtracted during centering.
-/

namespace DyadicCentralLinear

open Finset

private noncomputable def weight (p : ℕ) : ℝ :=
  if p.Prime then Real.log p else 0

private def window (n : ℕ) : Finset ℕ :=
  (range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.mod p 2 = 1)

private theorem card_bound (n : ℕ) : 6*(window n).card ≤ n+12 := by
  have bound : (window n).card ≤ (Icc (n/6) (n/3)).card := by
    apply card_le_card_of_injOn (fun p : ℕ => p/2)
    · intro p hp
      obtain ⟨_, hlo, hhi, _⟩ := mem_filter.mp hp
      apply mem_Icc.mpr
      change n/6 ≤ p/2 ∧ p/2 ≤ n/3
      constructor <;> omega
    · intro p hp t ht heq
      have hpo := (mem_filter.mp hp).2.2.2
      have hto := (mem_filter.mp ht).2.2.2
      change p % 2 = 1 at hpo
      change t % 2 = 1 at hto
      change p/2 = t/2 at heq
      omega
  rw [Nat.card_Icc] at bound
  omega

private theorem reflection (n : ℕ) (hn : Nat.mod n 2 = 0) :
    (∑ p ∈ window n, weight (n-p)) = ∑ p ∈ window n, weight p := by
  change n % 2 = 0 at hn
  have closed (p : ℕ) (hp : p ∈ window n) : n-p ∈ window n := by
    obtain ⟨hpr,hlo,hhi,hodd⟩ := mem_filter.mp hp
    have hpn := mem_range.mp hpr
    change p % 2 = 1 at hodd
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), by omega, by omega,
      (show (n-p) % 2 = 1 by omega)⟩
  apply sum_bij (fun p _ => n-p)
  · exact closed
  · intro p hp z hz h
    have hpn := mem_range.mp (mem_filter.mp hp).1
    have hzn := mem_range.mp (mem_filter.mp hz).1
    change n-p = n-z at h
    omega
  · intro p hp
    have hpn := mem_range.mp (mem_filter.mp hp).1
    exact ⟨n-p, closed p hp, by omega⟩
  · intro _ _; rfl

/-- The open lower endpoint in the theta difference can only reduce the
mass. Above 2 every prime in this interval belongs to the odd window. -/
private theorem theta_le_window (n : ℕ) (hn : 9 ≤ n) :
    Chebyshev.theta (2*(n:ℝ)/3) - Chebyshev.theta ((n:ℝ)/3) ≤
      ∑ p ∈ window n, weight p := by
  let a := (n:ℝ)/3
  let b := 2*(n:ℝ)/3
  let S := (⌊b⌋₊).primesLE \ (⌊a⌋₊).primesLE
  have hab : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono (by dsimp [a,b]; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hs : Chebyshev.theta b = (∑ p ∈ S, Real.log (p:ℝ)) + Chebyshev.theta a := by
    dsimp only [S]
    simp_rw [Chebyshev.theta_eq_sum_primesLE, sum_sdiff (Nat.primesLE_mono hab)]
  have hsub : S ⊆ window n := by
    intro p hp
    obtain ⟨hin, hout⟩ := mem_sdiff.mp hp
    obtain ⟨hub, hp'⟩ := Nat.mem_primesLE.mp hin
    have hlt : ⌊a⌋₊ < p := lt_of_not_ge (fun h => hout (Nat.mem_primesLE.mpr ⟨h,hp'⟩))
    have hpa := (Nat.floor_lt (show 0 ≤ a by dsimp [a]; positivity)).mp hlt
    have hpb := (Nat.le_floor_iff (show 0 ≤ b by dsimp [b]; positivity)).mp hub
    have hlo : n ≤ 3*p := by
      exact_mod_cast (show (n:ℝ) ≤ 3*(p:ℝ) by dsimp [a] at hpa; linarith)
    have hhi : 3*p ≤ 2*n := by
      exact_mod_cast (show 3*(p:ℝ) ≤ 2*(n:ℝ) by dsimp [b] at hpb; linarith)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hlo, hhi,
      Nat.odd_iff.mp (hp'.odd_of_ne_two (by omega))⟩
  change Chebyshev.theta b - Chebyshev.theta a ≤ _
  calc
    _ = ∑ p ∈ S, Real.log (p:ℝ) := by linarith
    _ = ∑ p ∈ S, weight p := by
      apply sum_congr rfl
      intro p hp
      simp only [weight, ite_eq_left (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _
      by_cases hp : p.Prime
      · simp [weight, hp, Real.log_natCast_nonneg]
      · simp [weight, hp]

end DyadicCentralLinear

open Finset DyadicCentralLinear

theorem Conjectures.Cuts.Taska5d9337be66b43f28ebbbdf7 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); ∀ (x2 : ℝ),   (0 : ℝ) < x2 →     ∃ (x4 : ℕ),       ∀ x5 ≥ x4,         have x7 : ℕ := (2 : ℕ) ^ x5;         have x8 : Finset ℕ := {x8 ∈ Finset.range (x7 + (1 : ℕ)) | x7 ≤ (3 : ℕ) * x8 ∧ (3 : ℕ) * x8 ≤ (2 : ℕ) * x7 ∧ x8 % (2 : ℕ) = (1 : ℕ)};         ((2 / 3 : ℝ) - x2) * ↑x7 ≤ ∑ x9 ∈ x8, ((2 : ℝ) * x1 x9 + (2 : ℝ) * x1 (x7 - x9) - (4 : ℝ))) := by
  dsimp only
  intro ε hε
  have low := Chebyshev.tendsto_theta_div_atTop.eventually_const_lt
    (by linarith : (1:ℝ) - ε/8 < 1)
  have high := Chebyshev.tendsto_theta_div_atTop.eventually_lt_const
    (by linarith : (1:ℝ) < 1 + ε/8)
  obtain ⟨x₀,hx₀⟩ := Filter.eventually_atTop.mp (low.and high)
  obtain ⟨U,hU⟩ := exists_nat_ge x₀
  obtain ⟨V,hV⟩ := exists_nat_ge (16/ε)
  refine ⟨max (max (3*U) V) 10, ?_⟩
  intro k hk
  let n : ℕ := 2^k
  have hkn : k < n := Nat.lt_two_pow_self
  have hn : 9 ≤ n := by omega
  have hlarge : (3:ℝ)*U ≤ n := by exact_mod_cast (show 3*U ≤ n by omega)
  have ha : x₀ ≤ (n:ℝ)/3 := by linarith
  have hb : x₀ ≤ 2*(n:ℝ)/3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h1 := (lt_div_iff₀ (by positivity : (0:ℝ)<2*(n:ℝ)/3)).mp (hx₀ _ hb).1
  have h2 := (div_lt_iff₀ (by positivity : (0:ℝ)<(n:ℝ)/3)).mp (hx₀ _ ha).2
  have herr := (div_le_iff₀ hε).mp (hV.trans (Nat.cast_le.mpr (by omega : V≤n)))
  have hcard : (6:ℝ)*(window n).card ≤ (n:ℝ)+12 := by exact_mod_cast card_bound n
  have hmass := theta_le_window n hn
  have hdvd : 2 ∣ n := dvd_pow_self 2 (by omega : k ≠ 0)
  have hrefl := reflection n (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  change ((2/3:ℝ)-ε)*n ≤ ∑ p ∈ window n, (2*weight p + 2*weight (n-p) - 4)
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hrefl]
  simp only [sum_const, nsmul_eq_mul]
  nlinarith only [h1,h2,herr,hcard,hmass]
