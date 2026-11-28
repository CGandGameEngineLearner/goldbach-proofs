import Mathlib

theorem Conjectures.Cuts.Taske81b0cb4098f12bf5a66eefc : (∀ m : ℕ, (Finset.range (m+1)).filter (fun r => 2*r^4 ≤ m^3) =
    Finset.range (min m (Nat.sqrt (Nat.sqrt (m^3/2)))+1)) := by
  intro m
  ext r
  simp only [Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff,le_min_iff]
  have e : r ≤ Nat.sqrt (Nat.sqrt (m^3/2)) ↔ 2*r^4 ≤ m^3 := by
    rw [Nat.le_sqrt,Nat.le_sqrt,Nat.le_div_iff_mul_le (by decide)]
    constructor <;> intro h <;> nlinarith only [h]
  rw [e]
