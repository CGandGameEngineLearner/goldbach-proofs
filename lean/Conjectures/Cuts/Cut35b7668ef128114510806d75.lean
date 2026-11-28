import Mathlib
import Conjectures.Goldbach.DynExceptionEnergy

open scoped BigOperators

-- Remove the varying odd-prime factor of the binary singular series.
-- child 1 zh: 每个合法的 13/225 短窗中，偶数端点的归一化对数权受限计数有统一的正均值下界。
-- child 1 en: In every admissible 13/225 window, the normalized log-weighted restricted count on even endpoints has a uniform positive mean floor.
-- child 2 zh: 每个合法短窗中，归一化对数权受限计数围绕该窗经验均值的平方偏差总和至多为 C(W+1)X^(-δ)。
-- child 2 en: In every admissible short window, the normalized log-weighted restricted count has total squared deviation from its empirical mean at most C(W+1)X^(-δ).
theorem Conjectures.Cuts.Cut35b7668ef128114510806d75
    (hMass :
      let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225))
      let E := fun y : ℕ => (Finset.Icc y (y + W y)).filter Even
      let A := fun (X n : ℕ) =>
        let pairs := ((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter
          (fun p => p ≤ n ∧ Nat.Prime (n - p))
        (∑ p ∈ pairs, Real.log (p : ℝ) * Real.log ((n - p : ℕ) : ℝ)) /
          (((Nat.sqrt X : ℝ) + 1) *
            ∏ q ∈ n.primeFactors.filter (fun q => 2 < q), ((q : ℝ) - 1) / ((q : ℝ) - 2))
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ X ≥ N, ∀ y : ℕ,
        X ≤ y → y + W y ≤ 2 * X →
        c ≤ (∑ n ∈ E y, A X n) / ((E y).card : ℝ))
    (hVariance :
      let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225))
      let E := fun y : ℕ => (Finset.Icc y (y + W y)).filter Even
      let A := fun (X n : ℕ) =>
        let pairs := ((Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter
          (fun p => p ≤ n ∧ Nat.Prime (n - p))
        (∑ p ∈ pairs, Real.log (p : ℝ) * Real.log ((n - p : ℕ) : ℝ)) /
          (((Nat.sqrt X : ℝ) + 1) *
            ∏ q ∈ n.primeFactors.filter (fun q => 2 < q), ((q : ℝ) - 1) / ((q : ℝ) - 2))
      ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ ∃ N : ℕ, ∀ X ≥ N, ∀ y : ℕ,
        X ≤ y → y + W y ≤ 2 * X →
        let μ := (∑ n ∈ E y, A X n) / ((E y).card : ℝ)
        (∑ n ∈ E y, (A X n - μ)^2) ≤ K * ((W y : ℝ) + 1) * (X : ℝ) ^ (-δ)) :
    (let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((13 : ℝ) / 225));
     let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime;
     let R := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card;
     ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
       X ≤ y → y + W y ≤ 2 * X →
       (((Finset.Icc y (y + W y)).filter (fun n => Even n ∧ R X n = 0)).card : ℝ) ≤
         C * ((W y : ℝ) + 1) * (X : ℝ) ^ (-δ)) := by
  intro W P R
  obtain ⟨c, hc, N₁, h₁⟩ := hMass
  obtain ⟨K, δ, hK, hδ, N₂, h₂⟩ := hVariance
  refine ⟨K / c^2, δ, by positivity, hδ, max N₁ N₂, ?_⟩
  intro X hX y hxy hy
  let E := (Finset.Icc y (y + W y)).filter Even
  let pairs := fun n : ℕ => (P X).filter (fun p => p ≤ n ∧ Nat.Prime (n - p))
  let A := fun n : ℕ =>
    (∑ p ∈ pairs n, Real.log (p : ℝ) * Real.log ((n - p : ℕ) : ℝ)) /
      (((Nat.sqrt X : ℝ) + 1) *
        ∏ q ∈ n.primeFactors.filter (fun q => 2 < q), ((q : ℝ) - 1) / ((q : ℝ) - 2))
  let μ := (∑ n ∈ E, A n) / (E.card : ℝ)
  have hMean : c ≤ μ := h₁ X ((le_max_left _ _).trans hX) y hxy hy
  have hSpread : (∑ n ∈ E, (A n - μ)^2) ≤ K * ((W y : ℝ) + 1) * (X : ℝ) ^ (-δ) :=
    h₂ X ((le_max_right _ _).trans hX) y hxy hy
  have hSubset : (Finset.Icc y (y + W y)).filter (fun n => Even n ∧ R X n = 0) ⊆
      E.filter (fun n => A n = 0) := by
    intro n hn
    obtain ⟨hWindow, hEven, hZero⟩ := Finset.mem_filter.mp hn
    have hEmpty : pairs n = ∅ := Finset.card_eq_zero.mp hZero
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hWindow, hEven⟩, by simp [A, hEmpty]⟩
  have hEnergy := Conjectures.Goldbach.DynExceptionEnergy E A (fun _ => μ) c hc (fun _ _ => hMean)
  have hCount := (le_div_iff₀ (show 0 < c^2 by positivity)).2 (hEnergy.trans hSpread)
  calc
    _ ≤ ((E.filter (fun n => A n = 0)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSubset
    _ ≤ _ := hCount.trans_eq (by ring)
