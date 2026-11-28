import Mathlib

/-!
# Cut of `L-goldbach-frontier-bv-three-fifths-level`

The frozen task is a level-`3/5` Bombieri-Vinogradov statement: for every `A > 0` there is a
constant `C` such that for all large `X` one can pick error bounds `B q` with
`max_a |ψ(X; q, a) - X/φ(q)| ≤ B q` for every `q ≤ X^(3/5)` and `Σ_{q ≤ X^(3/5)} B q ≤ C X (log X)^(-A)`.
The brief names the obstacle: this is strictly weaker than the Elliott-Halberstam conjecture but
it breaks the `1/2` barrier of the classical Bombieri-Vinogradov theorem, which is exactly what
the medium arcs need.

The moduli are split at the classical level `X^(1/2)`.  Two independent inputs are isolated;
the gluing is done in this file.

* `h₁` (classical range, known): the same statement with moduli restricted to `q ≤ X^(1/2)`.
  This is the shape of the Bombieri-Vinogradov theorem, with the bound read through an
  arbitrary function `B`.
* `h₂` (medium range, open): the same statement for the moduli `X^(1/2) < q ≤ X^(3/5)`.

Combination: for `X ≥ 1` the two ranges partition `[1, X^(3/5)]`, so `B q := B₁ q` on the
classical range and `B q := B₂ q` on the medium range has `Σ B q ≤ (C₁ + C₂) X (log X)^(-A)`.
-/

-- child 1 zh: 经典区间（已知）：对每个 A>0，存在 C 与阈值，使 q ≤ X^(1/2) 范围内的每个既约类上 ψ(X;q,a)−X/φ(q) 都不超过 B q，且 B q 在该范围上的和不超过 C·X/(log X)^A。
-- child 1 en: Classical range (known): for each A>0 there are C and a threshold such that for q at most X^(1/2) every coprime class has psi(X;q,a)-X/phi(q) bounded by B q, and the sum of B q over that range is at most C times X divided by (log X)^A.
-- child 2 zh: 中区间（开放前沿）：对每个 A>0，存在 C 与阈值，使 X^(1/2) < q ≤ X^(3/5) 范围内的每个既约类上 ψ(X;q,a)−X/φ(q) 都不超过 B q，且 B q 在该范围上的和不超过 C·X/(log X)^A。
-- child 2 en: Medium range (open frontier): for each A>0 there are C and a threshold such that for q with X^(1/2) < q at most X^(3/5) every coprime class has psi(X;q,a)-X/phi(q) bounded by B q, and the sum of B q over that range is at most C times X divided by (log X)^A.

theorem Conjectures.Cuts.Cut31cb02db070ad0a20e97a2f7
    (h₁ : ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧ ∀ X : ℕ, X₀ ≤ X → ∃ B : ℕ → ℝ,
      (∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q →
        |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) -
          (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧
      (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊, B q) ≤ C * (X : ℝ) / (Real.log (X : ℝ)) ^ A)
    (h₂ : ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧ ∀ X : ℕ, X₀ ≤ X → ∃ B : ℕ → ℝ,
      (∀ q ∈ Finset.Icc (⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊ + 1) ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, ∀ a : ℕ,
        Nat.Coprime a q →
        |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) -
          (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧
      (∑ q ∈ Finset.Icc (⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊ + 1) ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, B q) ≤
        C * (X : ℝ) / (Real.log (X : ℝ)) ^ A) :
    (∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧ ∀ X : ℕ, X₀ ≤ X → ∃ B : ℕ → ℝ, (∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q → |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧ (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, B q) ≤ C * (X : ℝ) / (Real.log (X : ℝ)) ^ A) := by
  intro A hA
  obtain ⟨C₁, X₁, hC₁, hX₁⟩ := h₁ A hA
  obtain ⟨C₂, X₂, hC₂, hX₂⟩ := h₂ A hA
  refine ⟨C₁ + C₂, max (max X₁ X₂) 1, by positivity, fun X hX => ?_⟩
  have hX₁' : X₁ ≤ X := by omega
  have hX₂' : X₂ ≤ X := by omega
  have hX1 : (1 : ℕ) ≤ X := by omega
  obtain ⟨B₁, hB₁, hB₁sum⟩ := hX₁ X hX₁'
  obtain ⟨B₂, hB₂, hB₂sum⟩ := hX₂ X hX₂'
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hmM : (⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℕ) ≤ ⌊(X : ℝ) ^ ((3 : ℝ) / 5)⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hXr (by norm_num))
  refine ⟨fun q => if q ≤ ⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ then B₁ q else B₂ q, ?_, ?_⟩
  · intro q hq a ha
    by_cases hqm : q ≤ ⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊
    · dsimp only
      rw [ite_eq_left hqm]
      exact hB₁ q (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1, hqm⟩) a ha
    · dsimp only
      rw [ite_eq_right hqm]
      exact hB₂ q (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hq).2⟩) a ha
  · have hu : Finset.Icc 1 ⌊(X : ℝ) ^ ((3 : ℝ) / 5)⌋₊ =
        Finset.Icc 1 ⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ ∪
          Finset.Icc (⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ + 1) ⌊(X : ℝ) ^ ((3 : ℝ) / 5)⌋₊ := by
      ext q
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    rw [hu, Finset.sum_union (Finset.disjoint_left.mpr (fun q hq1 hq2 => by
      have := Finset.mem_Icc.mp hq1
      have := Finset.mem_Icc.mp hq2
      omega))]
    have s1 : ∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊,
        (if q ≤ ⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ then B₁ q else B₂ q) =
        ∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊, B₁ q :=
      Finset.sum_congr rfl (fun q hq => by rw [ite_eq_left (Finset.mem_Icc.mp hq).2])
    have s2 : ∑ q ∈ Finset.Icc (⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ + 1) ⌊(X : ℝ) ^ ((3 : ℝ) / 5)⌋₊,
        (if q ≤ ⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ then B₁ q else B₂ q) =
        ∑ q ∈ Finset.Icc (⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ + 1) ⌊(X : ℝ) ^ ((3 : ℝ) / 5)⌋₊, B₂ q :=
      Finset.sum_congr rfl (fun q hq => by rw [ite_eq_right (by have := (Finset.mem_Icc.mp hq).1; omega)])
    rw [s1, s2]
    calc ∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊, B₁ q +
          ∑ q ∈ Finset.Icc (⌊(X : ℝ) ^ ((1 : ℝ) / 2)⌋₊ + 1) ⌊(X : ℝ) ^ ((3 : ℝ) / 5)⌋₊, B₂ q
        ≤ C₁ * (X : ℝ) / (Real.log (X : ℝ)) ^ A + C₂ * (X : ℝ) / (Real.log (X : ℝ)) ^ A := by
          exact add_le_add hB₁sum hB₂sum
      _ = (C₁ + C₂) * (X : ℝ) / (Real.log (X : ℝ)) ^ A := by ring
