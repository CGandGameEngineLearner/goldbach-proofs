import Mathlib
import Conjectures.Goldbach.Rfc11Top316AnchorBank
import Conjectures.Goldbach.Rfc11Top316FirstBankCover

namespace Rfc11Top316Repairs

private abbrev offsets : List ℕ :=
  [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299,
   55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561,
   59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117,
   18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269,
   71799, 73059, 66447]

private theorem repaired (i : ℕ) (hi : i ∈ [7564, 7909, 11134, 11329, 11989, 12154]) :
    ∃ t ∈ offsets, Nat.Prime (t - 2*i) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨71799, by decide, by norm_num⟩
  · exact ⟨73059, by decide, by norm_num⟩
  · exact ⟨71799, by decide, by norm_num⟩
  · exact ⟨66447, by decide, by norm_num⟩
  · exact ⟨73059, by decide, by norm_num⟩
  · exact ⟨71799, by decide, by norm_num⟩

private theorem covered (i : ℕ) (hlo : 1 ≤ i) (hhi : i ≤ 12288) :
    ∃ t ∈ offsets, Nat.Prime (t - 2*i) := by
  by_cases h : i ∈ [7564, 7909, 11134, 11329, 11989, 12154]
  · exact repaired i h
  · obtain ⟨t, ht, hp⟩ := (Conjectures.Goldbach.Rfc11Top316FirstBankCover i hlo hhi).2 h
    exact ⟨t, List.mem_of_mem_take ht, hp⟩

set_option exponentiation.threshold 400 in
theorem _root_.Conjectures.Goldbach.Rfc11Top316SixRepairs :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316-24576) (10^316) := by
  intro n hlo hhi heven
  let i := (10^316 - n) / 2
  have topEven : 2 ∣ (10:ℕ)^316 := by decide
  have hi : 1 ≤ i ∧ i ≤ 12288 := by dsimp [i]; omega
  obtain ⟨t, ht, hp⟩ := covered i hi.1 hi.2
  have small : ∀ s ∈ offsets, s ≤ 73059 := by decide
  have htop : 73059 ≤ (10:ℕ)^316 := by decide
  have hsub := hp.pos
  refine ⟨10^316-t, t-2*i, Conjectures.Goldbach.Rfc11Top316AnchorBank t ht, hp, ?_⟩
  have htBound := small t ht
  dsimp [i] at *
  omega

end Rfc11Top316Repairs
