import Conjectures.Goldbach.Rfc11Top316FirstBankCover
import Conjectures.Goldbach.Rfc11Top316AnchorBank

namespace Top316Repairs

private def bank : List ℕ := [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447]

private theorem completeBank (i : ℕ) (lo : 1 ≤ i) (hi : i ≤ 12288) :
    ∃ t ∈ bank, Nat.Prime (t - 2*i) := by
  by_cases h : i ∈ ([7564,7909,11134,11329,11989,12154] : List ℕ)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨71799, by decide, by norm_num⟩
    · exact ⟨73059, by decide, by norm_num⟩
    · exact ⟨71799, by decide, by norm_num⟩
    · exact ⟨66447, by decide, by norm_num⟩
    · exact ⟨73059, by decide, by norm_num⟩
    · exact ⟨71799, by decide, by norm_num⟩
  · obtain ⟨t, ht, hp⟩ := (Conjectures.Goldbach.Rfc11Top316FirstBankCover i lo hi).2 h
    exact ⟨t, List.mem_of_mem_take ht, hp⟩

private theorem offsetBound : ∀ t ∈ bank, t ≤ 73059 := by decide

end Top316Repairs

theorem Conjectures.Goldbach.Rfc11Top316SixRepairs : (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316-24576) (10^316) := by
  intro n hn hn' he
  obtain ⟨k, hk⟩ := he
  let T : ℕ := 10^316
  change T - 24576 ≤ n at hn
  change n < T at hn'
  have hT : T = 2 * (T / 2) := by decide +kernel
  let i := T / 2 - k
  have hlow : 1 ≤ i := by dsimp only [i]; omega
  have hhigh : i ≤ 12288 := by dsimp only [i]; omega
  obtain ⟨t, ht, hp⟩ := Top316Repairs.completeBank i hlow hhigh
  have hlarge := Conjectures.Goldbach.Rfc11Top316AnchorBank t ht
  refine ⟨T-t, t-2*i, hlarge, hp, ?_⟩
  have hpos := hp.two_le
  have hbound := Top316Repairs.offsetBound t ht
  have hcap : 73059 ≤ T := by decide +kernel
  dsimp only [i] at *
  omega
