import Mathlib

namespace PEqualNP.Outside

private theorem subCongr (t a b q : Int) :
    (t - a) % q = (t - b) % q ↔ a % q = b % q := by
  constructor <;> intro h
  · have hh := congrArg (fun z : Int => (t - z) % q) h
    simpa only [Int.sub_emod_emod, Int.sub_sub_self] using hh
  · have hh := congrArg (fun z : Int => (t - z) % q) h
    simpa only [Int.sub_emod_emod] using hh

private theorem reflectResidue (n q r k : Nat) (hk : k ≤ n) (hr : r < q) :
    (n - k) % q = (n + q - r) % q ↔ k % q = r := by
  have le : r ≤ n + q := by omega
  have h : (n : Int) + q - r = ((n : Int) - r) + q := by omega
  have hr' : (r : Int) % (q : Int) = r := by
    exact_mod_cast Nat.mod_eq_of_lt hr
  have equiv := subCongr (n : Int) (k : Int) (r : Int) (q : Int)
  rw [hr'] at equiv
  have wrap (a b : Int) : (a + b) % b = a % b := by
    simpa only [Int.mul_one] using Int.add_mul_emod_self_left a b 1
  have castMod (a b : Nat) : (a : Int) % (b : Int) = ((a % b : Nat) : Int) := rfl
  have target : ((n : Int) - k) % q = ((n : Int) + q - r) % q ↔ (k : Int) % q = r := by
    simpa only [h, wrap] using equiv
  simpa only [← Int.ofNat_sub hk, ← Int.natCast_add, ← Int.ofNat_sub le,
    castMod, Int.ofNat_inj] using target

theorem L_goldbach_coset_sum_reflection :
    let F := fun n q r : ℕ => (Finset.range (n + 1)).filter (fun k => k % q = r);
    let j := fun n q r : ℕ => (n + q - r) % q;
    ∀ n q r : ℕ, 0 < q → r < q → (F n q r).card = (F n q (j n q r)).card := by
  dsimp only
  intro n q r _hq hr
  refine Finset.card_bij' (fun k _ => n - k) (fun k _ => n - k) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, (reflectResidue n q r k (by omega) hr).2 hk.2⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    refine ⟨by omega, (reflectResidue n q r (n - k) (Nat.sub_le _ _) hr).1 ?_⟩
    rw [show n - (n - k) = k by omega]
    exact hk.2
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega

end PEqualNP.Outside
