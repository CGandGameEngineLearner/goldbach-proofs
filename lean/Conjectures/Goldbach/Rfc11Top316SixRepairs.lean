import Mathlib
import Conjectures.Goldbach.Rfc11Top316AnchorBank

namespace Conjectures.Goldbach

abbrev rfc11Anchors : List ℕ :=
  [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447]

def rfc11Hit (i : ℕ) : Bool :=
  rfc11Anchors.any (fun t => decide (2 * i < t) && decide (Nat.Prime (t - 2 * i)))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem rfc11Coverage : ∀ i ∈ Finset.Icc 1 12288, rfc11Hit i = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem Rfc11Top316SixRepairs :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo ≤ n → n < hi → 2 ∣ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316-24576) (10^316) := by
  intro n hlo hhi hev
  obtain ⟨k, rfl⟩ := hev
  set i : ℕ := 5*10^315 - k with hi
  have hi_le : i ≤ 12288 := by omega
  have hi_ge : 1 ≤ i := by omega
  have hcov := rfc11Coverage i (Finset.mem_Icc.mpr ⟨hi_ge, hi_le⟩)
  obtain ⟨t, ht_mem, ht⟩ := List.any_eq_true.mp hcov
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨hgt, hpr⟩ := ht
  refine ⟨10^316 - t, t - 2*i, ?_, hpr, ?_⟩
  · exact Rfc11Top316AnchorBank t ht_mem
  · omega

end Conjectures.Goldbach
