import Mathlib
import Conjectures.Goldbach.Rfc11Top316AnchorBank
import Conjectures.Goldbach.Rfc11Top316FirstBankCover

/-!
# Six-repair closure of the RFC11 upper boundary bank

`Rfc11Top316FirstBankCover` covers every even `n` in `(10^316 - 24576, 10^316)` except the
six offsets `[7564, 7909, 11134, 11329, 11989, 12154]`.  `Rfc11Top316AnchorBank` certifies
all 43 anchors while the cover only uses the first 40.

This file closes the six exceptions with the three reserved anchors `71799`, `73059`,
`66447`, giving the whole half-open interval with no exceptions.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 180000

namespace Conjectures.Goldbach

/-- The 43 anchors certified by `Rfc11Top316AnchorBank`. -/
def anchorOffsets : List ℕ :=
  [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117,
   58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939,
   42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821,
   8307, 14831, 15039, 60269, 71799, 73059, 66447]

/-- The six offsets left open by the first-bank cover. -/
def seamExceptions : List ℕ := [7564, 7909, 11134, 11329, 11989, 12154]

theorem anchorOffsets_le {t : ℕ} (ht : t ∈ anchorOffsets) : t ≤ 73059 := by
  have all : anchorOffsets.all (fun t => decide (t ≤ 73059)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all t ht)

theorem anchorOffsets_prime {t : ℕ} (ht : t ∈ anchorOffsets) : Nat.Prime (10^316 - t) :=
  Rfc11Top316AnchorBank t ht

/-- The three reserved anchors repair the six exceptions of the first-bank cover. -/
private theorem six_repair (i : ℕ) (hexc : i ∈ seamExceptions) :
    ∃ t ∈ anchorOffsets, Nat.Prime (t - 2*i) := by
  simp only [seamExceptions, List.mem_cons, List.not_mem_nil, or_false] at hexc
  rcases hexc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨71799, by decide +kernel, by norm_num⟩
  · exact ⟨73059, by decide +kernel, by norm_num⟩
  · exact ⟨71799, by decide +kernel, by norm_num⟩
  · exact ⟨66447, by decide +kernel, by norm_num⟩
  · exact ⟨73059, by decide +kernel, by norm_num⟩
  · exact ⟨71799, by decide +kernel, by norm_num⟩

/-- Every index of the bank has an anchor witness; the exception list is now irrelevant. -/
private theorem every_index_covered (i : ℕ) (hlo : 1 ≤ i) (hhi : i ≤ 12288) :
    ∃ t ∈ anchorOffsets, Nat.Prime (t - 2*i) := by
  by_cases hexc : i ∈ seamExceptions
  · exact six_repair i hexc
  · obtain ⟨t, ht, htp⟩ := (Rfc11Top316FirstBankCover i hlo hhi).mpr hexc
    refine ⟨t, ?_, htp⟩
    show t ∈ ([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077,
      35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341,
      41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893,
      1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ)
    exact List.mem_of_mem_take ht

/-- Converting an even offset back into a half-interval index. -/
private theorem interval_step (N : ℕ) (hN2 : 2 ∣ N)
    (hNhuge : 73059 < N)
    (hWit : ∀ i : ℕ, 1 ≤ i → i ≤ 12288 → ∃ t ∈ anchorOffsets, Nat.Prime (t - 2*i))
    (hAnchor : ∀ t ∈ anchorOffsets, Nat.Prime (N - t)) :
    ∀ n : ℕ, N - 24576 ≤ n → n < N → 2 ∣ n →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q = n := by
  intro n hnLo hnHi hnEven
  have hnLe : n ≤ N := Nat.le_of_lt hnHi
  have hSub : 2 ∣ N - n := Nat.dvd_sub hN2 hnEven
  obtain ⟨i, hi⟩ : ∃ i, N - n = 2*i := hSub
  have hiLo : 1 ≤ i := by omega
  have hiHi : i ≤ 12288 := by omega
  obtain ⟨t, ht, htp⟩ := hWit i hiLo hiHi
  have htLe : t ≤ 73059 := anchorOffsets_le ht
  have htN : t ≤ N := by omega
  have hqLe : 2*i ≤ t := by
    have h2 := htp.two_le
    omega
  refine ⟨N - t, t - 2*i, hAnchor t ht, htp, ?_⟩
  have : N - t + (t - 2*i) = N - (2*i) := by omega
  omega

/-- **Six repairs suffice.** Every even `n` in `(10^316 - 24576, 10^316)` is a sum of two primes. -/
theorem Rfc11Top316SixRepairs :
    ((fun (lo hi : ℕ) => ∀ n : ℕ, lo ≤ n → n < hi → 2 ∣ n →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316 - 24576) (10^316)) := by
  have hN2 : 2 ∣ (10^316 : ℕ) := by decide +kernel
  have hNhuge : (73059 : ℕ) < 10^316 := by decide +kernel
  exact interval_step (10^316) hN2 hNhuge every_index_covered
    (fun t ht => anchorOffsets_prime ht)

end Conjectures.Goldbach
