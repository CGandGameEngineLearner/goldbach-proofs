import Mathlib

open scoped BigOperators

/-!
This cut separates the one-point mass control from the two-point arithmetic input.
The mixed-difference identity turns their difference into the required covariance
budget.  The pair-mass premise is deliberately stated on the reflected central
cells, where it is the genuinely Goldbach-type input.  With cell masses bounded
by 101H/100 and BH = n/8, the product term is at most 10201n/80000; hence
8951n/80000 for the central pair mass is the exact threshold that leaves the
budget -n/64.
-/

theorem Conjectures.Cuts.Cutce62ba08925c6b3499363ed6
    -- child 1 zh: 二次幂反射块的短区间素数对数质量上界
    -- child 1 en: Uniform upper bound for prime-log mass on the reflected short cells
    (h_cell_mass :
      let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0;
      ∃ K : ℕ, ∀ k ≥ K,
        let n : ℕ := 2^k;
        let H : ℕ := 2^(k-k/4);
        let B : ℕ := 2^(k/4-3);
        let p := fun j t : ℕ => n/2 + j*H + t;
        let a := fun j t : ℕ => w (p j t);
        let b := fun j t : ℕ => w (n-p j t);
        ∀ j ∈ Finset.range B,
          (0 ≤ ∑ s ∈ Finset.range H, a j s ∧
            (∑ s ∈ Finset.range H, a j s) ≤ 101*(H : ℝ)/100) ∧
          (0 ≤ ∑ s ∈ Finset.range H, b j s ∧
            (∑ s ∈ Finset.range H, b j s) ≤ 101*(H : ℝ)/100))
    -- child 2 zh: 中心反射带内的二元素数相关下界
    -- child 2 en: Binary prime correlation floor on the central reflected band
    (h_pair_mass :
      let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0;
      ∃ K : ℕ, ∀ k ≥ K,
        let n : ℕ := 2^k;
        let H : ℕ := 2^(k-k/4);
        let B : ℕ := 2^(k/4-3);
        let p := fun j t : ℕ => n/2 + j*H + t;
        let a := fun j t : ℕ => w (p j t);
        let b := fun j t : ℕ => w (n-p j t);
        8951*(n : ℝ)/80000 ≤
          ∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H, a j s * b j s)
    :
    (let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0;
     ∃ K : ℕ, ∀ k ≥ K,
      let n : ℕ := 2^k;
      let H : ℕ := 2^(k-k/4);
      let B : ℕ := 2^(k/4-3);
      let p := fun j t : ℕ => n/2 + j*H + t;
      let a := fun j t : ℕ => w (p j t);
      let b := fun j t : ℕ => w (n-p j t);
      -(n : ℝ)/64 ≤
        ∑ j ∈ Finset.range B,
          (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
            (a j s-a j t) * (b j s-b j t)) / (2*(H : ℝ))) := by
  dsimp only
  let w : ℕ → ℝ := fun p => if Nat.Prime p then Real.log (p : ℝ) else 0
  have cell_identity (H : ℕ) (a b : ℕ → ℝ) :
      (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          (a s - a t) * (b s - b t))
        = 2 * ((H : ℝ) * (∑ s ∈ Finset.range H, a s * b s)
            - (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t)) := by
    have hexp : ∀ s t : ℕ,
        (a s - a t) * (b s - b t)
          = a s * b s - a s * b t - a t * b s + a t * b t := by
      intro s t
      ring
    have h1 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a s * b s)
        = (H : ℝ) * ∑ s ∈ Finset.range H, a s * b s := by
      have hinner : ∀ s : ℕ,
          (∑ t ∈ Finset.range H, a s * b s) = (H : ℝ) * (a s * b s) := by
        intro s
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [hinner]
      rw [← Finset.mul_sum]
    have h2 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a s * b t)
        = (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t) := by
      rw [Finset.sum_mul_sum]
    have h3 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a t * b s)
        = (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t) := by
      rw [Finset.sum_comm]
      rw [Finset.sum_mul_sum]
    have h4 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a t * b t)
        = (H : ℝ) * ∑ s ∈ Finset.range H, a s * b s := by
      rw [Finset.sum_comm]
      have hinner : ∀ t : ℕ,
          (∑ s ∈ Finset.range H, a t * b t) = (H : ℝ) * (a t * b t) := by
        intro t
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [hinner]
      rw [← Finset.mul_sum]
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4]
    ring
  have cell_term (H : ℕ) (hH : 0 < H) (a b : ℕ → ℝ) :
      (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          (a s - a t) * (b s - b t)) / (2 * (H : ℝ))
        = (∑ s ∈ Finset.range H, a s * b s)
            - (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t) / (H : ℝ) := by
    rw [cell_identity]
    have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
    field_simp
  rcases h_cell_mass with ⟨K₁, hmass⟩
  rcases h_pair_mass with ⟨K₂, hpair⟩
  refine ⟨max 12 (max K₁ K₂), ?_⟩
  intro k hk
  have hk12 : 12 ≤ k := le_trans (le_max_left _ _) hk
  have hk₁ : K₁ ≤ k :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk₂ : K₂ ≤ k :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  set n : ℕ := 2^k with hn
  set H : ℕ := 2^(k-k/4) with hH
  set B : ℕ := 2^(k/4-3) with hB
  set p : ℕ → ℕ → ℕ := fun j t => n/2 + j*H + t with hp
  set a : ℕ → ℕ → ℝ := fun j t => w (p j t) with ha
  set b : ℕ → ℕ → ℝ := fun j t => w (n-p j t) with hb
  have hHpos : 0 < H := by rw [hH]; positivity
  have hHreal : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  have hBH : B * H = 2^(k-3) := by
    rw [hB, hH, ← pow_add]
    congr 1
    omega
  have hn8 : (2 : ℕ)^(k-3) * 8 = 2^k := by
    have h : (2 : ℕ)^(k-3) * 8 = 2^(k-3) * 2^3 := by norm_num
    rw [h, ← pow_add]
    congr 1
    omega
  have hBH8 : B * H * 8 = n := by rw [hBH, hn8, hn]
  have hBHreal : (B : ℝ) * (H : ℝ) = (n : ℝ)/8 := by
    have h : ((B*H*8 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hBH8
    push_cast at h
    linarith
  have hmass_k : ∀ j ∈ Finset.range B,
      (0 ≤ ∑ s ∈ Finset.range H, a j s ∧
        (∑ s ∈ Finset.range H, a j s) ≤ 101*(H : ℝ)/100) ∧
      (0 ≤ ∑ s ∈ Finset.range H, b j s ∧
        (∑ s ∈ Finset.range H, b j s) ≤ 101*(H : ℝ)/100) := by
    simpa [w, hn, hH, hB, hp, ha, hb] using hmass k hk₁
  have hpair_k : 8951*(n : ℝ)/80000 ≤
      ∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H, a j s * b j s := by
    simpa [w, hn, hH, hB, hp, ha, hb] using hpair k hk₂
  have hmain_eq :
      (∑ j ∈ Finset.range B,
        (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          (a j s-a j t)*(b j s-b j t)) / (2*(H : ℝ)))
        = (∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H, a j s * b j s)
            - ∑ j ∈ Finset.range B,
                (∑ s ∈ Finset.range H, a j s) *
                  (∑ t ∈ Finset.range H, b j t) / (H : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.range B,
            ((∑ s ∈ Finset.range H, a j s * b j s)
              - (∑ s ∈ Finset.range H, a j s) *
                  (∑ t ∈ Finset.range H, b j t) / (H : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact cell_term H hHpos (a j) (b j)
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hbaseline :
      (∑ j ∈ Finset.range B,
        (∑ s ∈ Finset.range H, a j s) *
          (∑ t ∈ Finset.range H, b j t) / (H : ℝ))
        ≤ (10201 : ℝ)/80000 * (n : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range B, (10201 : ℝ)/10000 * (H : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            rcases hmass_k j hj with ⟨⟨hA0, hA⟩, ⟨hB0, hB⟩⟩
            have hU0 : 0 ≤ 101*(H : ℝ)/100 := by positivity
            have hAB :
                (∑ s ∈ Finset.range H, a j s) *
                    (∑ t ∈ Finset.range H, b j t)
                  ≤ (101*(H : ℝ)/100) * (101*(H : ℝ)/100) :=
              mul_le_mul hA hB hB0 hU0
            rw [div_le_iff₀ hHreal]
            nlinarith [hAB]
      _ = (B : ℝ) * ((10201 : ℝ)/10000 * (H : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (10201 : ℝ)/10000 * ((B : ℝ) * (H : ℝ)) := by ring
      _ = (10201 : ℝ)/10000 * ((n : ℝ)/8) := by rw [hBHreal]
      _ = (10201 : ℝ)/80000 * (n : ℝ) := by ring
  have htarget :
      -(n : ℝ)/64 ≤
        ∑ j ∈ Finset.range B,
          (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
            (a j s-a j t)*(b j s-b j t)) / (2*(H : ℝ)) := by
    rw [hmain_eq]
    have hgap : -(n : ℝ)/64 ≤
        (∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H, a j s * b j s)
          - ∑ j ∈ Finset.range B,
              (∑ s ∈ Finset.range H, a j s) *
                (∑ t ∈ Finset.range H, b j t) / (H : ℝ) := by
      linarith
    exact hgap
  simpa [w, hn, hH, hB, hp, ha, hb] using htarget
