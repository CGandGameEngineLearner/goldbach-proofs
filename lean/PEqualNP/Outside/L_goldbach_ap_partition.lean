import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_partition :
    let ap := fun (q a N : ℕ) (f : ℕ → ℝ) => Finset.sum ((Finset.range (N+1)).filter (fun k => k % q = a)) f; ∀ q N f, 0<q → Finset.sum (Finset.range q) (fun a => ap q a N f) = Finset.sum (Finset.range (N+1)) f := by
  dsimp only
  intro q N f hq
  have hmaps : ∀ k ∈ Finset.range (N + 1), k % q ∈ Finset.range q := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.mod_lt k hq)
  exact Finset.sum_fiberwise_of_maps_to (s := Finset.range (N + 1))
      (t := Finset.range q) (g := fun k => k % q) hmaps f
