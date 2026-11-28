import Mathlib

/-!
Premise 3/4 of a cut of L-goldbach-chen-coprime-shift-products.

The map `n ↦ (n + 2) / x2` is a bijection from the elements `n` of `x3` divisible (after the
shift by two) by `x2` onto the quotients `q` with `2 ≤ x2 * q` and `x2 * q - 2 ∈ x3`:

* forward, `x2 ∣ n + 2` gives `x2 * ((n + 2) / x2) = n + 2`, hence `2 ≤ x2 * q` and
  `x2 * q - 2 = n ∈ x3`; and `n ≤ x1` gives `q ≤ (x1 + 2) / x2`;
* backward, `2 ≤ x2 * q` makes `(x2 * q - 2) + 2 = x2 * q`, so `x2 ∣ (x2 * q - 2) + 2` and the
  quotient of that by `x2` is `q` again;
* injectivity is the same identity read in the other direction.

Self-contained: Mathlib only, no auxiliary declarations.
-/

theorem Conjectures.Cuts.Taskc8efccc5def347d802d54f58 :
    ∀ (x1 x2 : ℕ) (x3 : Finset ℕ), (0 : ℕ) < x2 → x3 ⊆ Finset.range (x1 + (1 : ℕ)) → {x6 ∈ x3 | x2 ∣ x6 + (2 : ℕ)}.card = {x6 ∈ Finset.range ((x1 + (2 : ℕ)) / x2 + (1 : ℕ)) | (2 : ℕ) ≤ x2 * x6 ∧ x2 * x6 - (2 : ℕ) ∈ x3}.card := by
  intro x1 x2 x3 hx2 hx3
  refine Finset.card_bij (fun (n : ℕ) _ => (n + (2 : ℕ)) / x2) ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn3, hdvd⟩ := Finset.mem_filter.mp hn
    have hnle : n ≤ x1 := by
      have := Finset.mem_range.mp (hx3 hn3)
      omega
    have hmul : x2 * ((n + (2 : ℕ)) / x2) = n + (2 : ℕ) := Nat.mul_div_cancel' hdvd
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
    · have hle : (n + (2 : ℕ)) / x2 ≤ (x1 + (2 : ℕ)) / x2 :=
        Nat.div_le_div_right (c := x2) (by omega)
      omega
    · rw [hmul]
      omega
    · have hsub : n + (2 : ℕ) - (2 : ℕ) = n := by omega
      rw [hmul, hsub]
      exact hn3
  · intro a ha b hb hab
    obtain ⟨_, hdva⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hdvb⟩ := Finset.mem_filter.mp hb
    have ha' : x2 * ((a + (2 : ℕ)) / x2) = a + (2 : ℕ) := Nat.mul_div_cancel' hdva
    have hb' : x2 * ((b + (2 : ℕ)) / x2) = b + (2 : ℕ) := Nat.mul_div_cancel' hdvb
    rw [hab] at ha'
    omega
  · intro q hq
    obtain ⟨_, h2q, hq3⟩ := Finset.mem_filter.mp hq
    refine ⟨x2 * q - (2 : ℕ), Finset.mem_filter.mpr ⟨hq3, ?_⟩, ?_⟩
    · have hq' : x2 * q - (2 : ℕ) + (2 : ℕ) = x2 * q := by omega
      exact ⟨q, hq'⟩
    · have hq' : x2 * q - (2 : ℕ) + (2 : ℕ) = x2 * q := by omega
      rw [hq', Nat.mul_div_cancel_left q hx2]
