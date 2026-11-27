import Mathlib
import Conjectures.Goldbach.Rfc11Top316AnchorBank
import Conjectures.Goldbach.Rfc11Top316FirstBankCover

/- Method. Every even n in the range is written as n = 10 ^ 316 - 2 * i with 1 <= i <= 12288.
For an index i outside the six gap indices, the first-bank cover gives an anchor t among the
first 40 offsets with t - 2 * i prime, and the anchor bank gives the prime 10 ^ 316 - t.
The six gaps are repaired with the last three anchors and a small prime. -/

theorem Conjectures.Goldbach.Rfc11Top316SixRepairs :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316-24576) (10^316) := by
  intro n hn1 hn2 hn
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 10 ^ 316 = N := ⟨_, rfl⟩
  rw [hN] at hn1 hn2
  have hNeven : 2 ∣ N := by
    rw [← hN, show (10 : ℕ) ^ 316 = 10 ^ 315 * 10 from pow_succ 10 315]
    exact dvd_mul_of_dvd_right (by decide) _
  have hNbig : 100000 ≤ N := by
    have h5 : (100000 : ℕ) = 10 ^ 5 := by decide
    rw [h5, ← hN]
    exact Nat.pow_le_pow_right (by decide) (by decide)
  obtain ⟨i, hi1, hi2, hi_eq⟩ : ∃ i : ℕ, 1 ≤ i ∧ i ≤ 12288 ∧ N - n = 2 * i := by
    obtain ⟨k, hk⟩ := hNeven
    obtain ⟨m, hm⟩ := hn
    refine ⟨k - m, ?_, ?_, ?_⟩ <;> omega
  have hn_eq : n = N - 2 * i := by omega
  have hcover : ∀ i : ℕ, 1 ≤ i → i ≤ 12288 →
      ((∃ t ∈ ([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ).take 40, Nat.Prime (t - 2 * i)) ↔ i ∉ ([7564, 7909, 11134, 11329, 11989, 12154] : List ℕ)) :=
    Conjectures.Goldbach.Rfc11Top316FirstBankCover
  by_cases hm : i ∈ ([7564, 7909, 11134, 11329, 11989, 12154] : List ℕ)
  · have hm6 : i = 7564 ∨ i = 7909 ∨ i = 11134 ∨ i = 11329 ∨ i = 11989 ∨ i = 12154 := by
      simpa [List.mem_cons, List.mem_singleton] using hm
    rcases hm6 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨56671, N - 71799, by norm_num, by
        have ha := Conjectures.Goldbach.Rfc11Top316AnchorBank 71799 (by decide)
        rw [hN] at ha
        exact ha, by omega⟩
    · exact ⟨57241, N - 73059, by norm_num, by
        have ha := Conjectures.Goldbach.Rfc11Top316AnchorBank 73059 (by decide)
        rw [hN] at ha
        exact ha, by omega⟩
    · exact ⟨49531, N - 71799, by norm_num, by
        have ha := Conjectures.Goldbach.Rfc11Top316AnchorBank 71799 (by decide)
        rw [hN] at ha
        exact ha, by omega⟩
    · exact ⟨43789, N - 66447, by norm_num, by
        have ha := Conjectures.Goldbach.Rfc11Top316AnchorBank 66447 (by decide)
        rw [hN] at ha
        exact ha, by omega⟩
    · exact ⟨49081, N - 73059, by norm_num, by
        have ha := Conjectures.Goldbach.Rfc11Top316AnchorBank 73059 (by decide)
        rw [hN] at ha
        exact ha, by omega⟩
    · exact ⟨47491, N - 71799, by norm_num, by
        have ha := Conjectures.Goldbach.Rfc11Top316AnchorBank 71799 (by decide)
        rw [hN] at ha
        exact ha, by omega⟩
  · obtain ⟨t, ht, hp⟩ := (hcover i hi1 hi2).mpr hm
    have hp2 : 2 ≤ t - 2 * i := hp.two_le
    have ht_full : t ∈ ([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ) := (List.take_sublist 40 [25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447]).mem ht
    have ht_le : t ≤ 73059 := by
      have ht43 :       t = 25787 ∨
          t = 23073 ∨
          t = 28121 ∨
          t = 30291 ∨
      t = 29519 ∨
          t = 51747 ∨
          t = 29183 ∨
          t = 30693 ∨
      t = 46539 ∨
          t = 27299 ∨
          t = 55077 ∨
          t = 35117 ∨
      t = 58401 ∨
          t = 48851 ∨
          t = 29673 ∨
          t = 44813 ∨
      t = 22041 ∨
          t = 52193 ∨
          t = 40623 ∨
          t = 35561 ∨
      t = 59667 ∨
          t = 54623 ∨
          t = 31341 ∨
          t = 41939 ∨
      t = 42603 ∨
          t = 49467 ∨
          t = 57963 ∨
          t = 12377 ∨
      t = 33269 ∨
          t = 18117 ∨
          t = 18191 ∨
          t = 42833 ∨
      t = 46341 ∨
          t = 38403 ∨
          t = 48893 ∨
          t = 1821 ∨
      t = 8307 ∨
          t = 14831 ∨
          t = 15039 ∨
          t = 60269 ∨
      t = 71799 ∨
          t = 73059 ∨
          t = 66447 := by
        simpa [List.mem_cons, List.mem_singleton] using ht_full
      rcases ht43 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have ha := Conjectures.Goldbach.Rfc11Top316AnchorBank t ht_full
    rw [hN] at ha
    exact ⟨t - 2 * i, N - t, hp, ha, by omega⟩
