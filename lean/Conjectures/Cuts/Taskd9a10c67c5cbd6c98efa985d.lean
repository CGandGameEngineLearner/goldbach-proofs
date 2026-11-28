import Mathlib

/-!
Premise 1/4 of a cut of L-goldbach-window-moving-prime-center.

A Goldbach pair `p + q = 2 * x1` is the same thing as a symmetric pair around the centre `x1`:
writing `k = |q - p| / 2` one has `{p, q} = {x1 - k, x1 + k}`.  Moreover `x1 - k` is a natural
number exactly when the smaller prime is at most the centre, and since `p + q = 2 * x1` forces
`min p q ≤ x1 ≤ max p q`, the witness `k ≤ x1` always exists.

The fourth-power window transfers verbatim: `dist p q = 2 * k`, so
`(2 * k) ^ 4 ≤ (2 * x1) ^ 3` is `16 * k ^ 4 ≤ 8 * x1 ^ 3`, i.e. `2 * k ^ 4 ≤ x1 ^ 3`.

Self-contained: Mathlib only.
-/

namespace Conjectures.Cuts.Taskd9a10c67c5cbd6c98efa985d_aux

/-- The window inequality in the two shapes used below. -/
private lemma window_iff (k x1 : ℕ) :
    (2 * k) ^ (4 : ℕ) ≤ (2 * x1) ^ (3 : ℕ) ↔ 2 * k ^ (4 : ℕ) ≤ x1 ^ (3 : ℕ) := by
  rw [show (2 * k) ^ (4 : ℕ) = 16 * k ^ (4 : ℕ) by ring,
    show (2 * x1) ^ (3 : ℕ) = 8 * x1 ^ (3 : ℕ) by ring]
  omega

end Conjectures.Cuts.Taskd9a10c67c5cbd6c98efa985d_aux

theorem Conjectures.Cuts.Taskd9a10c67c5cbd6c98efa985d :
    ∀ (x1 : ℕ), (∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Nat.Prime x3 ∧ x2 + x3 = (2 : ℕ) * x1 ∧ x2.dist x3 ^ (4 : ℕ) ≤ ((2 : ℕ) * x1) ^ (3 : ℕ)) ↔ ∃ x2 ≤ x1, (2 : ℕ) * x2 ^ (4 : ℕ) ≤ x1 ^ (3 : ℕ) ∧ Nat.Prime (x1 - x2) ∧ Nat.Prime (x1 + x2) := by
  intro x1
  constructor
  · rintro ⟨p, q, hp, hq, hsum, hdist⟩
    rcases le_total p q with hle | hle
    · have hpx : p ≤ x1 := by omega
      refine ⟨x1 - p, Nat.sub_le x1 p, ?_, ?_, ?_⟩
      · have hd : p.dist q = 2 * (x1 - p) := by
          rw [Nat.dist_eq_sub_of_le hle]
          omega
        have h4 : (2 * (x1 - p)) ^ (4 : ℕ) ≤ (2 * x1) ^ (3 : ℕ) := by
          rw [← hd]
          exact hdist
        exact (Conjectures.Cuts.Taskd9a10c67c5cbd6c98efa985d_aux.window_iff _ _).mp h4
      · have hsub : x1 - (x1 - p) = p := Nat.sub_sub_self hpx
        rw [hsub]
        exact hp
      · have hadd : x1 + (x1 - p) = q := by omega
        rw [hadd]
        exact hq
    · have hqx : q ≤ x1 := by omega
      refine ⟨x1 - q, Nat.sub_le x1 q, ?_, ?_, ?_⟩
      · have hd : p.dist q = 2 * (x1 - q) := by
          rw [Nat.dist_eq_sub_of_le_right hle]
          omega
        have h4 : (2 * (x1 - q)) ^ (4 : ℕ) ≤ (2 * x1) ^ (3 : ℕ) := by
          rw [← hd]
          exact hdist
        exact (Conjectures.Cuts.Taskd9a10c67c5cbd6c98efa985d_aux.window_iff _ _).mp h4
      · have hsub : x1 - (x1 - q) = q := Nat.sub_sub_self hqx
        rw [hsub]
        exact hq
      · have hadd : x1 + (x1 - q) = p := by omega
        rw [hadd]
        exact hp
  · rintro ⟨k, hk, hbound, hp, hq⟩
    refine ⟨x1 - k, x1 + k, hp, hq, ?_, ?_⟩
    · omega
    · have hd : (x1 - k).dist (x1 + k) = 2 * k := by
        rw [Nat.dist_eq_sub_of_le (by omega)]
        omega
      rw [hd]
      exact (Conjectures.Cuts.Taskd9a10c67c5cbd6c98efa985d_aux.window_iff _ _).mpr hbound
