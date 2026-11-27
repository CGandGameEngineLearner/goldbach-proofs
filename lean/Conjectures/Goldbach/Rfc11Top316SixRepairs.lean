import Mathlib
import Conjectures.Goldbach.Rfc11Top316AnchorBank
import Conjectures.Goldbach.Rfc11Top316FirstBankCover

set_option exponentiation.threshold 2000
set_option maxHeartbeats 400000

namespace Conjectures.Goldbach

/-- The 43 large prime anchors used by the V11/V12/V13 certificates. -/
def topList : List ℕ :=
  [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299,
   55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561,
   59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117,
   18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269,
   71799, 73059, 66447]

/-- Indices not covered by the first 40 anchors. -/
def excList : List ℕ := [7564, 7909, 11134, 11329, 11989, 12154]

theorem Rfc11Top316SixRepairs :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo ≤ n → n < hi → 2 ∣ n →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) (10^316 - 24576) (10^316) := by
  intro n hlo hhi heven
  let T : ℕ := 10^316
  change T - 24576 ≤ n at hlo
  change n < T at hhi
  have hTbig : 73059 < T := by dsimp [T]; norm_num
  have hT2 : 2 ∣ T := by dsimp [T]; norm_num
  have h2 : 2 ∣ T - n := Nat.dvd_sub hT2 heven
  let i : ℕ := (T - n) / 2
  have hdiv : T - n = 2 * i := by
    dsimp [i]
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel h2).symm
  have hpos : 0 < T - n := Nat.sub_pos_of_lt hhi
  have hi1 : 1 ≤ i := by omega
  have hi2 : i ≤ 12288 := by omega
  have hn : n = T - 2 * i := by omega
  by_cases hex : i ∈ excList
  · -- six exceptional indices, use the repair table
    simp only [excList, List.mem_cons, List.not_mem_nil, or_false] at hex
    rcases hex with h7564 | h7909 | h11134 | h11329 | h11989 | h12154
    · rw [h7564] at hn
      refine ⟨T - 71799, 56671, ?_, by norm_num, ?_⟩
      · have hmem : (71799 : ℕ) ∈ topList := by decide
        simpa [T] using Conjectures.Goldbach.Rfc11Top316AnchorBank 71799 hmem
      · omega
    · rw [h7909] at hn
      refine ⟨T - 73059, 57241, ?_, by norm_num, ?_⟩
      · have hmem : (73059 : ℕ) ∈ topList := by decide
        simpa [T] using Conjectures.Goldbach.Rfc11Top316AnchorBank 73059 hmem
      · omega
    · rw [h11134] at hn
      refine ⟨T - 71799, 49531, ?_, by norm_num, ?_⟩
      · have hmem : (71799 : ℕ) ∈ topList := by decide
        simpa [T] using Conjectures.Goldbach.Rfc11Top316AnchorBank 71799 hmem
      · omega
    · rw [h11329] at hn
      refine ⟨T - 66447, 43789, ?_, by norm_num, ?_⟩
      · have hmem : (66447 : ℕ) ∈ topList := by decide
        simpa [T] using Conjectures.Goldbach.Rfc11Top316AnchorBank 66447 hmem
      · omega
    · rw [h11989] at hn
      refine ⟨T - 73059, 49081, ?_, by norm_num, ?_⟩
      · have hmem : (73059 : ℕ) ∈ topList := by decide
        simpa [T] using Conjectures.Goldbach.Rfc11Top316AnchorBank 73059 hmem
      · omega
    · rw [h12154] at hn
      refine ⟨T - 71799, 47491, ?_, by norm_num, ?_⟩
      · have hmem : (71799 : ℕ) ∈ topList := by decide
        simpa [T] using Conjectures.Goldbach.Rfc11Top316AnchorBank 71799 hmem
      · omega
  · -- all other indices are covered by the first 40 anchors
    have hc := Conjectures.Goldbach.Rfc11Top316FirstBankCover
    dsimp only at hc
    have hcov : ∃ t ∈ topList.take 40, Nat.Prime (t - 2 * i) := by
      have := (hc i hi1 hi2).mpr (by simpa [excList] using hex)
      simpa [topList] using this
    rcases hcov with ⟨t, ht_take, hqprime⟩
    have ht_full : t ∈ topList := List.take_subset 40 topList ht_take
    have hpprime : Nat.Prime (T - t) := by
      have := Conjectures.Goldbach.Rfc11Top316AnchorBank t (by simpa [topList] using ht_full)
      simpa [T] using this
    have hall : topList.all (fun t => t ≤ 73059) := by decide
    have ht_bound : t ≤ 73059 := of_decide_eq_true ((List.all_eq_true.mp hall) t ht_full)
    have hq2 : 2 ≤ t - 2 * i := hqprime.two_le
    have h2i_le_t : 2 * i ≤ t := by omega
    have ht_le_T : t ≤ T := by omega
    refine ⟨T - t, t - 2 * i, hpprime, hqprime, ?_⟩
    have hsum : (T - t) + (t - 2 * i) = T - 2 * i := by omega
    omega

end Conjectures.Goldbach