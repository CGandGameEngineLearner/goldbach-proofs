import Mathlib

namespace PEqualNP.Outside

theorem L_log_rank_split_area_recurrence :
    ∀ n r c s : ℕ, r ≤ s → s < n → c ≤ n-(s+1) →
      let F := fun t => Nat.choose t r * Nat.choose (n-t) c;
      (s+1-r)*(n-s)*F (s+1) = (s+1)*(n-s-c)*F s := by
  intro n r c s hrs hsn hcn F
  have habs : ∀ {m k : ℕ}, k ≤ m → (m + 1 - k) * Nat.choose (m + 1) k = (m + 1) * Nat.choose m k := by
    intro m k hkm
    have h1 : Nat.choose m k = Nat.choose m (m - k) := by simp [Nat.choose_symm hkm]
    have hsub : m + 1 - k = m - k + 1 := by omega
    have hkm1 : k ≤ m + 1 := by omega
    have h2 : Nat.choose (m + 1) k = Nat.choose (m + 1) (m - k + 1) := by
      rw [← hsub]
      simp [Nat.choose_symm hkm1]
    rw [h1, h2, hsub, mul_comm, ← Nat.add_one_mul_choose_eq m (m - k)]
  have heq1 : (s + 1 - r) * Nat.choose (s + 1) r = (s + 1) * Nat.choose s r := habs hrs
  have heq2 : (n - s - c) * Nat.choose (n - s) c = (n - s) * Nat.choose (n - (s + 1)) c := by
    have h := habs hcn
    have hns : n - (s + 1) + 1 = n - s := by omega
    rw [hns] at h
    exact h
  change (s + 1 - r) * (n - s) * (Nat.choose (s + 1) r * Nat.choose (n - (s + 1)) c) =
      (s + 1) * (n - s - c) * (Nat.choose s r * Nat.choose (n - s) c)
  calc (s + 1 - r) * (n - s) * (Nat.choose (s + 1) r * Nat.choose (n - (s + 1)) c)
      = ((s + 1 - r) * Nat.choose (s + 1) r) * ((n - s) * Nat.choose (n - (s + 1)) c) := by ring
    _ = ((s + 1) * Nat.choose s r) * ((n - s - c) * Nat.choose (n - s) c) := by rw [heq1, ← heq2]
    _ = (s + 1) * (n - s - c) * (Nat.choose s r * Nat.choose (n - s) c) := by ring

end PEqualNP.Outside
