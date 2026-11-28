import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Tactic

private lemma central_theta_lower (ε : ℝ) (he : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1/3 - ε) * (n : ℝ) ≤
      Chebyshev.theta (2 * (n : ℝ) / 3) - Chebyshev.theta ((n : ℝ) / 3) := by
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp Chebyshev.tendsto_theta_div_atTop) ε he
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * max T 1)
  refine ⟨N, fun n hn => ?_⟩
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have ht₁ := le_max_left T (1 : ℝ)
  have ht₂ := le_max_right T (1 : ℝ)
  have hn' : (0 : ℝ) < (n : ℝ) := by linarith
  have hL := (hT (2 * (n : ℝ) / 3) (by linarith))
  have hR := (hT ((n : ℝ) / 3) (by linarith))
  rw [Real.dist_eq, abs_lt] at hL hR
  have hL' : 1 - ε < Chebyshev.theta (2 * (n : ℝ) / 3) / (2 * (n : ℝ) / 3) := by
    linarith only [hL.1]
  have hR' : Chebyshev.theta ((n : ℝ) / 3) / ((n : ℝ) / 3) < 1 + ε := by
    linarith only [hR.2]
  have hl := (lt_div_iff₀ (by positivity : 0 < 2 * (n : ℝ) / 3)).mp hL'
  have hr := (div_lt_iff₀ (by positivity : 0 < (n : ℝ) / 3)).mp hR'
  linarith only [hl, hr]

private lemma central_weight_lower (n : ℕ) (hn : 9 ≤ n) :
    Chebyshev.theta (2*(n:ℝ)/3) - Chebyshev.theta ((n:ℝ)/3) ≤
      ∑ p ∈ ((Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.mod p 2 = 1)),
        (if Nat.Prime p then Real.log (p:ℝ) else 0) := by
  have hf : ⌊(n:ℝ)/3⌋₊ ≤ ⌊2*(n:ℝ)/3⌋₊ :=
    Nat.floor_mono (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
    ← Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hf), ← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hhi,hlo⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hhi, hprime⟩ := Nat.mem_primesLE.mp hhi
    have hnlo : ¬p ≤ ⌊(n:ℝ)/3⌋₊ :=
      fun h => hlo (Nat.mem_primesLE.mpr ⟨h,hprime⟩)
    have hupper : (p:ℝ) ≤ 2*(n:ℝ)/3 := (Nat.le_floor_iff (by positivity)).mp hhi
    have hlower : (n:ℝ)/3 < p :=
      lt_of_not_ge (fun h => hnlo ((Nat.le_floor_iff (by positivity)).mpr h))
    have l : n < 3*p := by exact_mod_cast (show (n:ℝ) < 3*(p:ℝ) by linarith)
    have u : 3*p ≤ 2*n := by exact_mod_cast (show 3*(p:ℝ) ≤ 2*(n:ℝ) by linarith)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      l.le,u,hprime.mod_two_eq_one_iff_ne_two.mpr (by omega)⟩, hprime⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)

private lemma central_card_upper (n : ℕ) :
    (((Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.mod p 2 = 1)).card : ℝ)
      ≤ (n:ℝ)/6+2 := by
  let s := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.mod p 2 = 1)
  change (s.card : ℝ) ≤ _
  have hcard : s.card ≤ (Finset.Icc (n/6) (n/3)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ => p/2)
    · intro p hp
      have h := (Finset.mem_filter.mp (show p ∈ s from hp)).2
      apply Finset.mem_Icc.mpr
      change n/6 ≤ p/2 ∧ p/2 ≤ n/3
      constructor <;> omega
    · intro p hp q hq heq
      have hp' := (Finset.mem_filter.mp (show p ∈ s from hp)).2.2.2
      have hq' := (Finset.mem_filter.mp (show q ∈ s from hq)).2.2.2
      change p/2 = q/2 at heq
      omega
  rw [Nat.card_Icc] at hcard
  have hnat : 6 * s.card ≤ n + 12 := by omega
  have hreal : 6 * (s.card : ℝ) ≤ (n:ℝ) + 12 := by exact_mod_cast hnat
  linarith

private lemma central_reflection (n : ℕ) (hn : Even n) (w : ℕ → ℝ) :
    let A := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.mod p 2 = 1)
    ∑ p ∈ A, w (n-p) = ∑ p ∈ A, w p := by
  intro A
  have mem (p : ℕ) : p ∈ A ↔ p < n+1 ∧ n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.mod p 2 = 1 := by
    simp [A]
  obtain ⟨m, hm⟩ := hn
  have maps : ∀ p ∈ A, n-p ∈ A := by
    intro p hp
    apply (mem _).2
    have := (mem _).1 hp
    omega
  have inv : ∀ p ∈ A, n-(n-p) = p := by
    intro p hp
    have := (mem _).1 hp
    omega
  exact Finset.sum_nbij' (n - ·) (n - ·) maps maps inv inv (fun _ _ => rfl)

private lemma central_finish (ε : ℝ) (n : ℕ) (hn : Even n) (w : ℕ → ℝ)
    (hbudget : 16 ≤ ε * (n:ℝ)) :
    let A := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.mod p 2 = 1)
    (1/3-ε/8)*(n:ℝ) ≤ ∑ p ∈ A, w p →
    (A.card : ℝ) ≤ (n:ℝ)/6+2 →
    (2/3-ε)*(n:ℝ) ≤ ∑ p ∈ A, (2*w p + 2*w (n-p) - 4) := by
  intro A hmass hcard
  have hr : ∑ p ∈ A, w (n-p) = ∑ p ∈ A, w p := central_reflection n hn w
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr]
  simp only [Finset.sum_const, nsmul_eq_mul]
  linarith

theorem Conjectures.Cuts.Taska5d9337be66b43f28ebbbdf7 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); ∀ (x2 : ℝ),   (0 : ℝ) < x2 →     ∃ (x4 : ℕ),       ∀ x5 ≥ x4,         have x7 : ℕ := (2 : ℕ) ^ x5;         have x8 : Finset ℕ := {x8 ∈ Finset.range (x7 + (1 : ℕ)) | x7 ≤ (3 : ℕ) * x8 ∧ (3 : ℕ) * x8 ≤ (2 : ℕ) * x7 ∧ x8 % (2 : ℕ) = (1 : ℕ)};         ((2 / 3 : ℝ) - x2) * ↑x7 ≤ ∑ x9 ∈ x8, ((2 : ℝ) * x1 x9 + (2 : ℝ) * x1 (x7 - x9) - (4 : ℝ))) := by
  intro w ε he
  obtain ⟨N, hN⟩ := central_theta_lower (ε/8) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_ge (16/ε)
  refine ⟨max 9 (max N M), ?_⟩
  intro k hk n A
  have hkn : k ≤ n := k.lt_two_pow_self.le
  have hn₉ : 9 ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hnM : M ≤ n := by omega
  have hε : 16 ≤ ε * (n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ he).mp (hM.trans (by exact_mod_cast hnM))
  have hEven : Even n := Even.pow_of_ne_zero (by decide : Even (2:ℕ)) (by omega : k ≠ 0)
  exact central_finish ε n hEven w hε
    ((hN n hnN).trans (central_weight_lower n hn₉)) (central_card_upper n)
