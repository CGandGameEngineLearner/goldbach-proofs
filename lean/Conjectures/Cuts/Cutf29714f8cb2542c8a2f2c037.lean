import Mathlib

open Filter

-- child 1 zh: 对充分大的 N，在 q² ≤ N ≤ 4q² 的素分母区间内，距互素分数 a/q 至多 1/q² 的实频率处，冯·曼戈尔特和的振幅至多为 N^(4/5+δ)，对每个 δ>0 成立。
-- child 1 en: For each δ>0, the Mangoldt sum is eventually at most N^(4/5+δ) in norm within 1/q² of any reduced fraction a/q with prime q and q² ≤ N ≤ 4q².
-- child 2 zh: 每个素分母各选一个互素分子。振幅大于 N^(17/24) 且至多为 N^(3/4) 的分母个数，最终至多为 N^(5/12+δ)，对每个 δ>0 成立。
-- child 2 en: For every choice of reduced numerators, the number of prime denominators in the prescribed band with amplitude in (N^(17/24), N^(3/4)] is eventually at most N^(5/12+δ) for each δ>0.
-- child 3 zh: 每个素分母各选一个互素分子。振幅大于 N^(3/4) 的分母个数，最终至多为 N^(19/60+δ)，对每个 δ>0 成立。
-- child 3 en: For every choice of reduced numerators, the number of prime denominators in the prescribed band with amplitude above N^(3/4) is eventually at most N^(19/60+δ) for each δ>0.

private theorem sum_sq_on_band {x u v : ℝ} (hx : 0 < x) (B : Finset ℕ) (F : ℕ → ℝ)
    (hF : ∀ q, 0 ≤ F q) (hcard : (B.card : ℝ) ≤ x^u)
    (hcap : ∀ q ∈ B, F q ≤ x^v) :
    (∑ q ∈ B, (F q)^2) ≤ x^(u + 2*v) := by
  calc
    _ ≤ ∑ _ ∈ B, (x^v)^2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact pow_le_pow_left₀ (hF q) (hcap q hq) 2
    _ = (B.card : ℝ) * (x^v)^2 := by simp
    _ ≤ x^u * (x^v)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = x^(u + 2*v) := by
      rw [two_mul, Real.rpow_add hx, Real.rpow_add hx, sq]

theorem Conjectures.Cuts.Cutf29714f8cb2542c8a2f2c037
    (hcap :
      let S := fun (N : ℕ) (x : ℝ) => ∑ m ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I)
      ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ N q a : ℕ, K ≤ N → 2 ≤ N →
        Nat.Prime q → q^2 ≤ N → N ≤ 4*q^2 → a < q → Nat.Coprime a q →
        ∀ θ : ℝ, |θ - (a : ℝ)/(q : ℝ)| ≤ 1/(q : ℝ)^2 →
          ‖S N θ‖ ≤ (N : ℝ)^(4/5 + δ))
    (hmed :
      let S := fun (N : ℕ) (x : ℝ) => ∑ m ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I)
      ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ N : ℕ, K ≤ N → 2 ≤ N →
        ∀ a : ℕ → ℕ, (∀ q : ℕ, Nat.Prime q → a q < q ∧ Nat.Coprime (a q) q) →
          let Q := (Finset.Icc 2 N.sqrt).filter (fun q => Nat.Prime q ∧ N ≤ 4*q^2)
          let F := fun q : ℕ => ‖S N ((a q : ℝ)/(q : ℝ))‖
          ((Q.filter (fun q => (N : ℝ)^(17/24 : ℝ) < F q ∧ F q ≤ (N : ℝ)^(3/4 : ℝ))).card : ℝ)
            ≤ (N : ℝ)^(5/12 + δ))
    (hhigh :
      let S := fun (N : ℕ) (x : ℝ) => ∑ m ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I)
      ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ N : ℕ, K ≤ N → 2 ≤ N →
        ∀ a : ℕ → ℕ, (∀ q : ℕ, Nat.Prime q → a q < q ∧ Nat.Coprime (a q) q) →
          let Q := (Finset.Icc 2 N.sqrt).filter (fun q => Nat.Prime q ∧ N ≤ 4*q^2)
          let F := fun q : ℕ => ‖S N ((a q : ℝ)/(q : ℝ))‖
          ((Q.filter (fun q => (N : ℝ)^(3/4 : ℝ) < F q)).card : ℝ) ≤ (N : ℝ)^(19/60 + δ)) :
    (let S := fun (N : ℕ) (x : ℝ) => ∑ m ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I); ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ a : ℕ → ℕ, (∀ q : ℕ, Nat.Prime q → a q < q ∧ Nat.Coprime (a q) q) → (∑ q ∈ (Finset.Icc 2 N.sqrt).filter (fun q => Nat.Prime q ∧ N ≤ 4*q^2), ‖S N ((a q : ℝ)/(q : ℝ))‖^2) ≤ (N : ℝ)^((23 : ℝ)/12+η)) := by
  classical
  intro S η hη
  let δ := η/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K₁, h₁⟩ := hcap δ hδ
  obtain ⟨K₂, h₂⟩ := hmed δ hδ
  obtain ⟨K₃, h₃⟩ := hhigh δ hδ
  obtain ⟨K₄, h₄⟩ := (eventually_atTop.1
    (((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (3 : ℝ))))
  refine ⟨max (max K₁ K₂) (max K₃ K₄), ?_⟩
  intro N hN hN₂ a ha
  let x : ℝ := N
  let Q := (Finset.Icc 2 N.sqrt).filter (fun q => Nat.Prime q ∧ N ≤ 4*q^2)
  let F := fun q : ℕ => ‖S N ((a q : ℝ)/(q : ℝ))‖
  let low := Q.filter (fun q => F q ≤ x^(17/24 : ℝ))
  let rest := Q.filter (fun q => ¬ F q ≤ x^(17/24 : ℝ))
  let mid := rest.filter (fun q => F q ≤ x^(3/4 : ℝ))
  let hi := rest.filter (fun q => ¬ F q ≤ x^(3/4 : ℝ))
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ N by omega)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hF (q : ℕ) : 0 ≤ F q := norm_nonneg _
  have hlcard : (low.card : ℝ) ≤ x^(1/2 : ℝ) := by
    have hq : low.card ≤ N.sqrt := by
      calc
        _ ≤ Q.card := Finset.card_filter_le _ _
        _ ≤ (Finset.Icc 2 N.sqrt).card := Finset.card_filter_le _ _
        _ ≤ N.sqrt := by rw [Nat.card_Icc]; omega
    calc
      _ ≤ (N.sqrt : ℝ) := by exact_mod_cast hq
      _ ≤ Real.sqrt x := Real.nat_sqrt_le_real_sqrt
      _ = _ := Real.sqrt_eq_rpow x
  have hl := sum_sq_on_band hxpos low F hF hlcard (fun q hq => (Finset.mem_filter.mp hq).2)
  have hmcard : (mid.card : ℝ) ≤ x^(5/12 + δ) := by
    have H := h₂ N (by omega) hN₂ a ha
    simpa only [mid, rest, Q, F, x, S, Finset.filter_filter, not_le, and_assoc] using H
  have hm := sum_sq_on_band hxpos mid F hF hmcard (fun q hq => (Finset.mem_filter.mp hq).2)
  have hhcard : (hi.card : ℝ) ≤ x^(19/60 + δ) := by
    have H : ((Q.filter (fun q => x^(3/4 : ℝ) < F q)).card : ℝ) ≤ x^(19/60+δ) :=
      h₃ N (by omega) hN₂ a ha
    refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans H
    intro q hq
    obtain ⟨hr, hu⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, lt_of_not_ge hu⟩
  have hhcap (q : ℕ) (hq : q ∈ hi) : F q ≤ x^(4/5+δ) := by
    have hqQ : q ∈ Q := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    obtain ⟨hI, hprime, hsize⟩ := Finset.mem_filter.mp hqQ
    have hsq : q^2 ≤ N := by simpa [sq] using Nat.le_sqrt.mp (Finset.mem_Icc.mp hI).2
    exact h₁ N q (a q) (by omega) hN₂ hprime hsq hsize (ha q hprime).1
      (ha q hprime).2 _ (by rw [sub_self, abs_zero]; positivity)
  have hh := sum_sq_on_band hxpos hi F hF hhcard hhcap
  let b : ℝ := 23/12 + 3*δ
  have L : x^(1/2 + 2*(17/24) : ℝ) ≤ x^b :=
    Real.rpow_le_rpow_of_exponent_le hx (by dsimp [b]; linarith)
  have M : x^((5/12 + δ) + 2*(3/4)) ≤ x^b :=
    Real.rpow_le_rpow_of_exponent_le hx (by dsimp [b]; linarith)
  have H : x^((19/60 + δ) + 2*(4/5 + δ)) ≤ x^b :=
    Real.rpow_le_rpow_of_exponent_le hx (by dsimp [b]; linarith)
  have hsplit₁ := Finset.sum_filter_add_sum_filter_not Q (fun q => F q ≤ x^(17/24 : ℝ)) (fun q => (F q)^2)
  have hsplit₂ := Finset.sum_filter_add_sum_filter_not rest (fun q => F q ≤ x^(3/4 : ℝ)) (fun q => (F q)^2)
  change (∑ q ∈ low, F q ^ 2) + (∑ q ∈ rest, F q ^ 2) = ∑ q ∈ Q, F q ^ 2 at hsplit₁
  change (∑ q ∈ mid, F q ^ 2) + (∑ q ∈ hi, F q ^ 2) = ∑ q ∈ rest, F q ^ 2 at hsplit₂
  change (∑ q ∈ Q, F q ^ 2) ≤ x^(23/12+η)
  calc
    _ ≤ 3 * x^b := by linarith only [hsplit₁, hsplit₂, hl.trans L, hm.trans M, hh.trans H]
    _ ≤ x^δ * x^b :=
      mul_le_mul_of_nonneg_right (h₄ N (by omega)) (Real.rpow_nonneg hxpos.le _)
    _ = _ := by rw [← Real.rpow_add hxpos]; congr 1; dsimp [b, δ]; ring
