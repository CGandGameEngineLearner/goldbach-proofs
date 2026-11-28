import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt

-- Every possible least divisor in this finite interval is at most 128.
private def oddPrimeCheck (n : ℕ) : Bool :=
  decide (2 ≤ n ∧ n < 129 * 129 ∧ n % 2 = 1) &&
    (List.range 127).all fun k =>
      decide (n < (k + 2) * (k + 2) ∨ n % (k + 2) ≠ 0)

private theorem oddPrimeCheck_sound {n : ℕ} (h : oddPrimeCheck n = true) :
    n.Prime ∧ Odd n := by
  simp only [oddPrimeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hn, hmax, hodd⟩, hdiv⟩ := h
  refine ⟨Nat.prime_def_le_sqrt.mpr ⟨hn, ?_⟩, Nat.odd_iff.mpr hodd⟩
  intro d hd hs hdvd
  have hsmax : n.sqrt < 129 := Nat.sqrt_lt.mpr hmax
  have hk := hdiv (d - 2) (by omega)
  rw [Nat.sub_add_cancel hd] at hk
  exact hk.elim (Nat.not_lt.mpr (Nat.le_sqrt.mp hs)) (fun h => h (Nat.mod_eq_zero_of_dvd hdvd))

-- These small first summands suffice throughout the range.
private def firstPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 73, 79]

private def hasPair (i : ℕ) : Bool :=
  let n := 16 * (i + 1)
  firstPrimes.any fun p => decide (p ≤ n) && oddPrimeCheck p && oddPrimeCheck (n - p)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem allPairs : (List.range 1024).all hasPair = true := by decide +kernel

theorem Conjectures.Cuts.Taskdc0a505371b58c19da53c009 : (have x1 : ℕ → Prop := fun (x1 : ℕ) => ∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Odd x2 ∧ Nat.Prime x3 ∧ Odd x3 ∧ x2 + x3 = x1; ∀ x2 < (1024 : ℕ), x1 ((16 : ℕ) * (x2 + (1 : ℕ)))) := by
  dsimp only
  intro i hi
  have hc := (List.all_eq_true.mp allPairs) i (List.mem_range.mpr hi)
  simp only [hasPair, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨p, _, ⟨hle, hp⟩, hq⟩ := hc
  obtain ⟨hp', hop⟩ := oddPrimeCheck_sound hp
  obtain ⟨hq', hoq⟩ := oddPrimeCheck_sound hq
  exact ⟨p, 16 * (i + 1) - p, hp', hop, hq', hoq, by omega⟩
