import Mathlib

-- Adapted to the modulus 510510 from the project's Apache-2.0 proof for 30030:
-- lean/PEqualNP/Outside/L_goldbach_finite_residue_rough_30030.lean
private def shifts : List ℕ := [3, 5, 7, 11, 41, 61, 79, 149, 167, 769, 1747, 2297, 2311]

private def covered (i : ℕ) : Bool :=
  shifts.any fun p => ((2 * i + 510510 - p) % 510510).gcd 510510 == 1

-- A block of depth d tests the half-residues in [s, s + 2^d).
private def blockOK (s : ℕ) : ℕ → Bool
  | 0 => covered s
  | d + 1 => blockOK s d && blockOK (s + 2^d) d

private theorem covered_in_block {s d i : ℕ} (hb : blockOK s d = true)
    (lo : s ≤ i) (hi : i < s + 2^d) : covered i = true := by
  induction d generalizing s with
  | zero =>
    have he : s = i := by simp at hi; omega
    subst i
    exact hb
  | succ d ih =>
    simp only [blockOK, Bool.and_eq_true] at hb
    rw [pow_succ] at hi
    by_cases h : i < s + 2^d
    · exact ih hb.1 lo h
    · exact ih hb.2 (by omega) (by omega)

-- Check disjoint blocks separately, using only Lean's kernel reduction.
set_option maxHeartbeats 4000000 in
private theorem block_0_12 : blockOK 0 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_4096_12 : blockOK 4096 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_8192_12 : blockOK 8192 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_12288_12 : blockOK 12288 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_16384_12 : blockOK 16384 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_20480_12 : blockOK 20480 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_24576_12 : blockOK 24576 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_28672_12 : blockOK 28672 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_32768_12 : blockOK 32768 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_36864_12 : blockOK 36864 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_40960_12 : blockOK 40960 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_45056_12 : blockOK 45056 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_49152_12 : blockOK 49152 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_53248_12 : blockOK 53248 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_57344_12 : blockOK 57344 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_61440_12 : blockOK 61440 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_65536_12 : blockOK 65536 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_69632_12 : blockOK 69632 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_73728_12 : blockOK 73728 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_77824_12 : blockOK 77824 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_81920_12 : blockOK 81920 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_86016_12 : blockOK 86016 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_90112_12 : blockOK 90112 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_94208_12 : blockOK 94208 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_98304_12 : blockOK 98304 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_102400_12 : blockOK 102400 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_106496_12 : blockOK 106496 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_110592_12 : blockOK 110592 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_114688_12 : blockOK 114688 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_118784_12 : blockOK 118784 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_122880_12 : blockOK 122880 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_126976_12 : blockOK 126976 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_131072_12 : blockOK 131072 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_135168_12 : blockOK 135168 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_139264_12 : blockOK 139264 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_143360_12 : blockOK 143360 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_147456_12 : blockOK 147456 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_151552_12 : blockOK 151552 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_155648_12 : blockOK 155648 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_159744_12 : blockOK 159744 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_163840_12 : blockOK 163840 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_167936_12 : blockOK 167936 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_172032_12 : blockOK 172032 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_176128_12 : blockOK 176128 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_180224_12 : blockOK 180224 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_184320_12 : blockOK 184320 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_188416_12 : blockOK 188416 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_192512_12 : blockOK 192512 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_196608_12 : blockOK 196608 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_200704_12 : blockOK 200704 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_204800_12 : blockOK 204800 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_208896_12 : blockOK 208896 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_212992_12 : blockOK 212992 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_217088_12 : blockOK 217088 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_221184_12 : blockOK 221184 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_225280_12 : blockOK 225280 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_229376_12 : blockOK 229376 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_233472_12 : blockOK 233472 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_237568_12 : blockOK 237568 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_241664_12 : blockOK 241664 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_245760_12 : blockOK 245760 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_249856_12 : blockOK 249856 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_253952_12 : blockOK 253952 12 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem block_258048_12 : blockOK 258048 12 = true := by decide +kernel

private theorem block_0_13 : blockOK 0 13 = true := by
  change (blockOK 0 12 && blockOK 4096 12) = true
  rw [block_0_12, block_4096_12]

private theorem block_8192_13 : blockOK 8192 13 = true := by
  change (blockOK 8192 12 && blockOK 12288 12) = true
  rw [block_8192_12, block_12288_12]

private theorem block_16384_13 : blockOK 16384 13 = true := by
  change (blockOK 16384 12 && blockOK 20480 12) = true
  rw [block_16384_12, block_20480_12]

private theorem block_24576_13 : blockOK 24576 13 = true := by
  change (blockOK 24576 12 && blockOK 28672 12) = true
  rw [block_24576_12, block_28672_12]

private theorem block_32768_13 : blockOK 32768 13 = true := by
  change (blockOK 32768 12 && blockOK 36864 12) = true
  rw [block_32768_12, block_36864_12]

private theorem block_40960_13 : blockOK 40960 13 = true := by
  change (blockOK 40960 12 && blockOK 45056 12) = true
  rw [block_40960_12, block_45056_12]

private theorem block_49152_13 : blockOK 49152 13 = true := by
  change (blockOK 49152 12 && blockOK 53248 12) = true
  rw [block_49152_12, block_53248_12]

private theorem block_57344_13 : blockOK 57344 13 = true := by
  change (blockOK 57344 12 && blockOK 61440 12) = true
  rw [block_57344_12, block_61440_12]

private theorem block_65536_13 : blockOK 65536 13 = true := by
  change (blockOK 65536 12 && blockOK 69632 12) = true
  rw [block_65536_12, block_69632_12]

private theorem block_73728_13 : blockOK 73728 13 = true := by
  change (blockOK 73728 12 && blockOK 77824 12) = true
  rw [block_73728_12, block_77824_12]

private theorem block_81920_13 : blockOK 81920 13 = true := by
  change (blockOK 81920 12 && blockOK 86016 12) = true
  rw [block_81920_12, block_86016_12]

private theorem block_90112_13 : blockOK 90112 13 = true := by
  change (blockOK 90112 12 && blockOK 94208 12) = true
  rw [block_90112_12, block_94208_12]

private theorem block_98304_13 : blockOK 98304 13 = true := by
  change (blockOK 98304 12 && blockOK 102400 12) = true
  rw [block_98304_12, block_102400_12]

private theorem block_106496_13 : blockOK 106496 13 = true := by
  change (blockOK 106496 12 && blockOK 110592 12) = true
  rw [block_106496_12, block_110592_12]

private theorem block_114688_13 : blockOK 114688 13 = true := by
  change (blockOK 114688 12 && blockOK 118784 12) = true
  rw [block_114688_12, block_118784_12]

private theorem block_122880_13 : blockOK 122880 13 = true := by
  change (blockOK 122880 12 && blockOK 126976 12) = true
  rw [block_122880_12, block_126976_12]

private theorem block_131072_13 : blockOK 131072 13 = true := by
  change (blockOK 131072 12 && blockOK 135168 12) = true
  rw [block_131072_12, block_135168_12]

private theorem block_139264_13 : blockOK 139264 13 = true := by
  change (blockOK 139264 12 && blockOK 143360 12) = true
  rw [block_139264_12, block_143360_12]

private theorem block_147456_13 : blockOK 147456 13 = true := by
  change (blockOK 147456 12 && blockOK 151552 12) = true
  rw [block_147456_12, block_151552_12]

private theorem block_155648_13 : blockOK 155648 13 = true := by
  change (blockOK 155648 12 && blockOK 159744 12) = true
  rw [block_155648_12, block_159744_12]

private theorem block_163840_13 : blockOK 163840 13 = true := by
  change (blockOK 163840 12 && blockOK 167936 12) = true
  rw [block_163840_12, block_167936_12]

private theorem block_172032_13 : blockOK 172032 13 = true := by
  change (blockOK 172032 12 && blockOK 176128 12) = true
  rw [block_172032_12, block_176128_12]

private theorem block_180224_13 : blockOK 180224 13 = true := by
  change (blockOK 180224 12 && blockOK 184320 12) = true
  rw [block_180224_12, block_184320_12]

private theorem block_188416_13 : blockOK 188416 13 = true := by
  change (blockOK 188416 12 && blockOK 192512 12) = true
  rw [block_188416_12, block_192512_12]

private theorem block_196608_13 : blockOK 196608 13 = true := by
  change (blockOK 196608 12 && blockOK 200704 12) = true
  rw [block_196608_12, block_200704_12]

private theorem block_204800_13 : blockOK 204800 13 = true := by
  change (blockOK 204800 12 && blockOK 208896 12) = true
  rw [block_204800_12, block_208896_12]

private theorem block_212992_13 : blockOK 212992 13 = true := by
  change (blockOK 212992 12 && blockOK 217088 12) = true
  rw [block_212992_12, block_217088_12]

private theorem block_221184_13 : blockOK 221184 13 = true := by
  change (blockOK 221184 12 && blockOK 225280 12) = true
  rw [block_221184_12, block_225280_12]

private theorem block_229376_13 : blockOK 229376 13 = true := by
  change (blockOK 229376 12 && blockOK 233472 12) = true
  rw [block_229376_12, block_233472_12]

private theorem block_237568_13 : blockOK 237568 13 = true := by
  change (blockOK 237568 12 && blockOK 241664 12) = true
  rw [block_237568_12, block_241664_12]

private theorem block_245760_13 : blockOK 245760 13 = true := by
  change (blockOK 245760 12 && blockOK 249856 12) = true
  rw [block_245760_12, block_249856_12]

private theorem block_253952_13 : blockOK 253952 13 = true := by
  change (blockOK 253952 12 && blockOK 258048 12) = true
  rw [block_253952_12, block_258048_12]

private theorem block_0_14 : blockOK 0 14 = true := by
  change (blockOK 0 13 && blockOK 8192 13) = true
  rw [block_0_13, block_8192_13]

private theorem block_16384_14 : blockOK 16384 14 = true := by
  change (blockOK 16384 13 && blockOK 24576 13) = true
  rw [block_16384_13, block_24576_13]

private theorem block_32768_14 : blockOK 32768 14 = true := by
  change (blockOK 32768 13 && blockOK 40960 13) = true
  rw [block_32768_13, block_40960_13]

private theorem block_49152_14 : blockOK 49152 14 = true := by
  change (blockOK 49152 13 && blockOK 57344 13) = true
  rw [block_49152_13, block_57344_13]

private theorem block_65536_14 : blockOK 65536 14 = true := by
  change (blockOK 65536 13 && blockOK 73728 13) = true
  rw [block_65536_13, block_73728_13]

private theorem block_81920_14 : blockOK 81920 14 = true := by
  change (blockOK 81920 13 && blockOK 90112 13) = true
  rw [block_81920_13, block_90112_13]

private theorem block_98304_14 : blockOK 98304 14 = true := by
  change (blockOK 98304 13 && blockOK 106496 13) = true
  rw [block_98304_13, block_106496_13]

private theorem block_114688_14 : blockOK 114688 14 = true := by
  change (blockOK 114688 13 && blockOK 122880 13) = true
  rw [block_114688_13, block_122880_13]

private theorem block_131072_14 : blockOK 131072 14 = true := by
  change (blockOK 131072 13 && blockOK 139264 13) = true
  rw [block_131072_13, block_139264_13]

private theorem block_147456_14 : blockOK 147456 14 = true := by
  change (blockOK 147456 13 && blockOK 155648 13) = true
  rw [block_147456_13, block_155648_13]

private theorem block_163840_14 : blockOK 163840 14 = true := by
  change (blockOK 163840 13 && blockOK 172032 13) = true
  rw [block_163840_13, block_172032_13]

private theorem block_180224_14 : blockOK 180224 14 = true := by
  change (blockOK 180224 13 && blockOK 188416 13) = true
  rw [block_180224_13, block_188416_13]

private theorem block_196608_14 : blockOK 196608 14 = true := by
  change (blockOK 196608 13 && blockOK 204800 13) = true
  rw [block_196608_13, block_204800_13]

private theorem block_212992_14 : blockOK 212992 14 = true := by
  change (blockOK 212992 13 && blockOK 221184 13) = true
  rw [block_212992_13, block_221184_13]

private theorem block_229376_14 : blockOK 229376 14 = true := by
  change (blockOK 229376 13 && blockOK 237568 13) = true
  rw [block_229376_13, block_237568_13]

private theorem block_245760_14 : blockOK 245760 14 = true := by
  change (blockOK 245760 13 && blockOK 253952 13) = true
  rw [block_245760_13, block_253952_13]

private theorem block_0_15 : blockOK 0 15 = true := by
  change (blockOK 0 14 && blockOK 16384 14) = true
  rw [block_0_14, block_16384_14]

private theorem block_32768_15 : blockOK 32768 15 = true := by
  change (blockOK 32768 14 && blockOK 49152 14) = true
  rw [block_32768_14, block_49152_14]

private theorem block_65536_15 : blockOK 65536 15 = true := by
  change (blockOK 65536 14 && blockOK 81920 14) = true
  rw [block_65536_14, block_81920_14]

private theorem block_98304_15 : blockOK 98304 15 = true := by
  change (blockOK 98304 14 && blockOK 114688 14) = true
  rw [block_98304_14, block_114688_14]

private theorem block_131072_15 : blockOK 131072 15 = true := by
  change (blockOK 131072 14 && blockOK 147456 14) = true
  rw [block_131072_14, block_147456_14]

private theorem block_163840_15 : blockOK 163840 15 = true := by
  change (blockOK 163840 14 && blockOK 180224 14) = true
  rw [block_163840_14, block_180224_14]

private theorem block_196608_15 : blockOK 196608 15 = true := by
  change (blockOK 196608 14 && blockOK 212992 14) = true
  rw [block_196608_14, block_212992_14]

private theorem block_229376_15 : blockOK 229376 15 = true := by
  change (blockOK 229376 14 && blockOK 245760 14) = true
  rw [block_229376_14, block_245760_14]

private theorem block_0_16 : blockOK 0 16 = true := by
  change (blockOK 0 15 && blockOK 32768 15) = true
  rw [block_0_15, block_32768_15]

private theorem block_65536_16 : blockOK 65536 16 = true := by
  change (blockOK 65536 15 && blockOK 98304 15) = true
  rw [block_65536_15, block_98304_15]

private theorem block_131072_16 : blockOK 131072 16 = true := by
  change (blockOK 131072 15 && blockOK 163840 15) = true
  rw [block_131072_15, block_163840_15]

private theorem block_196608_16 : blockOK 196608 16 = true := by
  change (blockOK 196608 15 && blockOK 229376 15) = true
  rw [block_196608_15, block_229376_15]

private theorem block_0_17 : blockOK 0 17 = true := by
  change (blockOK 0 16 && blockOK 65536 16) = true
  rw [block_0_16, block_65536_16]

private theorem block_131072_17 : blockOK 131072 17 = true := by
  change (blockOK 131072 16 && blockOK 196608 16) = true
  rw [block_131072_16, block_196608_16]

private theorem block_0_18 : blockOK 0 18 = true := by
  change (blockOK 0 17 && blockOK 131072 17) = true
  rw [block_0_17, block_131072_17]

theorem Conjectures.Goldbach.FiniteResidueRough510510 :
    ∀ a : ℕ, a < 510510 → Even a → ∃ p ∈ ({3,5,7,11,41,61,79,149,167,769,1747,2297,2311} : Finset ℕ), Nat.Coprime ((a+510510-p)%510510) 510510 := by
  intro a ha he
  obtain ⟨i, rfl⟩ := he
  have hi : i < 0 + 2^18 := by norm_num; omega
  have h := covered_in_block block_0_18 (Nat.zero_le _) hi
  obtain ⟨p, hp, hg⟩ := List.any_eq_true.mp h
  refine ⟨p, ?_, ?_⟩
  · simpa [shifts] using hp
  · simpa [Nat.Coprime, two_mul] using hg
