import Mathlib

namespace GoldbachMod18Counting

private abbrev residues : Finset ℕ := {1, 5, 11, 13, 17}

private abbrev admissible (r i : ℕ) : Prop :=
  i % 18 ∈ residues ∧ (r + 18 - i % 18) % 18 ∈ residues

private def blocks (r k : ℕ) : ℕ :=
  ((Finset.range (18 * k)).filter (admissible r)).card

-- The count_add' induction also appears in Problem337.periodic_count_mul
-- in Conjectures.TwinPrimes.CofactorTwoLinearSieve.
private theorem repeated_count {p : ℕ → Prop} [DecidablePred p]
    {d : ℕ} (hp : Function.Periodic p d) (k : ℕ) :
    Nat.count p (k * d) = k * Nat.count p d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.count_add']
    have hshift : (fun i => p (i + d)) = p := funext hp
    simp only [hshift, ih]
    ring

private theorem blocks_mul (r k : ℕ) : blocks r k = k * blocks r 1 := by
  have hp : Function.Periodic (admissible r) 18 := by
    intro i
    simp only [admissible, Nat.add_mod_right]
  simpa only [Nat.count_eq_card_filter_range, blocks, Nat.mul_one, Nat.mul_comm 18 k]
    using repeated_count hp k

-- The finite check covers only the target residues in one period.
set_option maxRecDepth 4096 in
private theorem one_block : ∀ r : Fin 18, r.val % 2 = 0 → 1 ≤ blocks r.val 1 := by
  decide

end GoldbachMod18Counting

open GoldbachMod18Counting

theorem Conjectures.Cuts.Taskbd367fa3aeb676e8acffa6f7 :
    (have x1 : Finset ℕ := {(1 : ℕ), (5 : ℕ), (11 : ℕ), (13 : ℕ), (17 : ℕ)}; have x2 : ℕ → ℕ → ℕ := fun (x2 x3 : ℕ) => {x4 ∈ Finset.range ((18 : ℕ) * x3) | x4 % (18 : ℕ) ∈ x1 ∧ (x2 % (18 : ℕ) + (18 : ℕ) - x4 % (18 : ℕ)) % (18 : ℕ) ∈ x1}.card; ∀ (x3 x4 : ℕ), Even x3 → x4 ≤ x2 x3 x4 ∧ x2 x3 x4 = x4 * x2 x3 (1 : ℕ)) := by
  change ∀ n k : ℕ, Even n →
    k ≤ blocks (n % 18) k ∧ blocks (n % 18) k = k * blocks (n % 18) 1
  intro n k hn
  have hr : (n % 18) % 2 = 0 := by
    obtain ⟨a, ha⟩ := hn
    omega
  have hpos := one_block ⟨n % 18, Nat.mod_lt _ (by decide)⟩ hr
  have heq := blocks_mul (n % 18) k
  refine ⟨?_, heq⟩
  rw [heq]
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hpos
