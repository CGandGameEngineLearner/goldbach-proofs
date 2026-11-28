import Mathlib

-- child 1 zh: 三次时至少一侧有重复，或更高次时两侧均有重复，证明这些碰撞满足原题的计数上界。
-- child 1 en: Bound collisions with repetition on either side for cubics and on both sides in higher degree.
-- child 2 zh: 三次时两侧各自无重复，或更高次时至少一侧无重复，在原题的排除条件下控制剩余碰撞。
-- child 2 en: Bound the remaining collisions, with both tuples injective for cubics or at least one injective in higher degree.
open Finset in
theorem Conjectures.Cuts.Cutf57646e21d68930c69c52674
    (hrepeat : ∀ (P : Polynomial ℤ), 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
      let T := Fintype.piFinset fun _ : Fin 4 => A
      let weight (a : Fin 4 → ℕ) := ∑ i, P.eval (a i : ℤ)
      let D := (T.product T).filter fun z => weight z.1 = weight z.2 ∧
        ∀ i : Fin 4 × Fin 4, z.1 i.1 ≠ z.2 i.2
      let G := D.filter fun z => ∀ (i j : Fin 4 × Fin 4), i.1 ≠ i.2 → j.1 ≠ j.2 →
        z.1 i.1 + z.1 i.2 ≠ z.2 j.1 + z.2 j.2 ∧
        z.1 i.1 ^ 2 + z.1 i.2 ^ 2 ≠ z.2 j.1 ^ 2 + z.2 j.2 ^ 2
      let repeated (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) :=
        if P.natDegree = 3 then ¬ Function.Injective z.1 ∨ ¬ Function.Injective z.2
        else ¬ Function.Injective z.1 ∧ ¬ Function.Injective z.2
      ((G.filter repeated).card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^(if P.natDegree = 3 then 5 else 4))
    (hrest : ∀ (P : Polynomial ℤ), 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
      let T := Fintype.piFinset fun _ : Fin 4 => A
      let weight (a : Fin 4 → ℕ) := ∑ i, P.eval (a i : ℤ)
      let D := (T.product T).filter fun z => weight z.1 = weight z.2 ∧
        ∀ i : Fin 4 × Fin 4, z.1 i.1 ≠ z.2 i.2
      let G := D.filter fun z => ∀ (i j : Fin 4 × Fin 4), i.1 ≠ i.2 → j.1 ≠ j.2 →
        z.1 i.1 + z.1 i.2 ≠ z.2 j.1 + z.2 j.2 ∧
        z.1 i.1 ^ 2 + z.1 i.2 ^ 2 ≠ z.2 j.1 ^ 2 + z.2 j.2 ^ 2
      let repeated (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) :=
        if P.natDegree = 3 then ¬ Function.Injective z.1 ∨ ¬ Function.Injective z.2
        else ¬ Function.Injective z.1 ∧ ¬ Function.Injective z.2
      ((G.filter fun z => ¬ repeated z).card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^(if P.natDegree = 3 then 5 else 4)) :
    (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (_ : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 → x15.1 ≠ x15.2 → x13.1 x14.1 + x13.1 x14.2 ≠ x13.2 x15.1 + x13.2 x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) ≠ x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := by
  classical
  intro P hd ε hε
  obtain ⟨C,hC,hc⟩ := hrepeat P hd ε hε
  obtain ⟨D,hD,hd'⟩ := hrest P hd ε hε
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro M hM A hA
  let T := Fintype.piFinset fun _ : Fin 4 => A
  let w (a : Fin 4 → ℕ) := ∑ i, P.eval (a i : ℤ)
  let B := (T.product T).filter fun z => w z.1 = w z.2 ∧ ∀ i : Fin 4 × Fin 4, z.1 i.1 ≠ z.2 i.2
  let G := B.filter fun z => ∀ i j : Fin 4 × Fin 4, i.1 ≠ i.2 → j.1 ≠ j.2 →
    z.1 i.1 + z.1 i.2 ≠ z.2 j.1 + z.2 j.2 ∧ z.1 i.1 ^ 2 + z.1 i.2 ^ 2 ≠ z.2 j.1 ^ 2 + z.2 j.2 ^ 2
  let rep (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) :=
    if P.natDegree = 3 then ¬ Function.Injective z.1 ∨ ¬ Function.Injective z.2
    else ¬ Function.Injective z.1 ∧ ¬ Function.Injective z.2
  let W := (M : ℝ)^ε * (A.card : ℝ)^(if P.natDegree = 3 then 5 else 4)
  have h1 : ((G.filter rep).card : ℝ) ≤ C * W := by
    simpa only [W, ← mul_assoc] using hc M hM A hA
  have h2 : ((G.filter fun z => ¬ rep z).card : ℝ) ≤ D * W := by
    simpa only [W, ← mul_assoc] using hd' M hM A hA
  have ht : (G.card : ℝ) = ((G.filter rep).card : ℝ) + ((G.filter fun z => ¬ rep z).card : ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s := G) rep).symm
  change (G.card : ℝ) ≤ (C+D) * (M : ℝ)^ε * _
  rw [ht,mul_assoc,add_mul]
  exact add_le_add h1 h2
