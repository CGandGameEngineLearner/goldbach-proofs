import Mathlib
import Conjectures.Goldbach.Rfc11Top316AnchorBank
import Conjectures.Goldbach.Rfc11Top316FirstBankCover

namespace Rfc11Top316Repair

def offsets : List ℕ :=
  [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299,
   55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561,
   59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117,
   18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269,
   71799, 73059, 66447]

def exceptions : List ℕ := [7564, 7909, 11134, 11329, 11989, 12154]

private theorem pair_of_offset {T i t : ℕ} (ha : (T - t).Prime)
    (hb : (t - 2*i).Prime) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = T - 2*i := by
  have hpa := ha.two_le
  have hpb := hb.two_le
  exact ⟨T - t, t - 2*i, ha, hb, by omega⟩

private theorem small_prime {n : ℕ} (hn : n ≤ 60269) (h : Rfc11SmallPrime.check n = true) :
    n.Prime :=
  (Rfc11SmallPrime.check_correct hn).mp h

set_option maxRecDepth 20000 in
private theorem repairs (hBank : ∀ t ∈ offsets, Nat.Prime (10^316-t)) {i : ℕ}
    (he : i ∈ exceptions) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 10^316 - 2*i := by
  simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_of_offset (i := 7564) (hBank 71799 (by decide +kernel))
      (small_prime (by decide) (by decide +kernel))
  · exact pair_of_offset (i := 7909) (hBank 73059 (by decide +kernel))
      (small_prime (by decide) (by decide +kernel))
  · exact pair_of_offset (i := 11134) (hBank 71799 (by decide +kernel))
      (small_prime (by decide) (by decide +kernel))
  · exact pair_of_offset (i := 11329) (hBank 66447 (by decide +kernel))
      (small_prime (by decide) (by decide +kernel))
  · exact pair_of_offset (i := 11989) (hBank 73059 (by decide +kernel))
      (small_prime (by decide) (by decide +kernel))
  · exact pair_of_offset (i := 12154) (hBank 71799 (by decide +kernel))
      (small_prime (by decide) (by decide +kernel))

set_option maxRecDepth 20000 in
theorem from_certificates (hBank : ∀ t ∈ offsets, Nat.Prime (10^316-t))
    (hFirst : ∀ i : ℕ, 1 ≤ i → i ≤ 12288 →
      ((∃ t ∈ offsets.take 40, Nat.Prime (t-2*i)) ↔ i ∉ exceptions)) :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316-24576) (10^316) := by
  intro n hlo hhi heven
  have hcut : 2 ∣ (10 : ℕ)^316 := dvd_pow (by decide : 2 ∣ (10 : ℕ)) (by decide)
  obtain ⟨i, hi⟩ := Nat.dvd_sub hcut heven
  have hiLower : 1 ≤ i := by omega
  have hiUpper : i ≤ 12288 := by omega
  have hn : n = 10^316 - 2*i := by omega
  rw [hn]
  by_cases he : i ∈ exceptions
  · exact repairs hBank he
  · obtain ⟨t, ht, hp⟩ := (hFirst i hiLower hiUpper).mpr he
    exact pair_of_offset (hBank t (List.mem_of_mem_take ht)) hp

end Rfc11Top316Repair

set_option maxRecDepth 20000 in
theorem Conjectures.Goldbach.Rfc11Top316SixRepairs :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316-24576) (10^316) := by
  exact Rfc11Top316Repair.from_certificates
    Conjectures.Goldbach.Rfc11Top316AnchorBank
    Conjectures.Goldbach.Rfc11Top316FirstBankCover
