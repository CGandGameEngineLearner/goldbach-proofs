import Mathlib.Tactic.Primality
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Insert

namespace PostBoundaryCertificates

private theorem prime_1069 : Nat.Prime 1069 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 89] }])

private theorem prime_1283 : Nat.Prime 1283 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 641] }])

private theorem prime_1301 : Nat.Prime 1301 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13] }])

private theorem prime_1307 : Nat.Prime 1307 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 653] }])

private theorem prime_1579 : Nat.Prime 1579 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 263] }])

private theorem prime_1871 : Nat.Prime 1871 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }])

private theorem prime_2087 : Nat.Prime 2087 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 149] }])

private theorem prime_2719 : Nat.Prime 2719 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 151] }])

private theorem prime_3583 : Nat.Prime 3583 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 199] }])

private theorem prime_4073 : Nat.Prime 4073 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 509] }])

private theorem prime_4093 : Nat.Prime 4093 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 31] }])

private theorem prime_6421 : Nat.Prime 6421 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 107] }])

private theorem prime_7577 : Nat.Prime 7577 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 947] }])

private theorem prime_8147 : Nat.Prime 8147 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 4073] }]) [prime_4073]

private theorem prime_8429 : Nat.Prime 8429 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 43] }])

private theorem prime_14407 : Nat.Prime 14407 := by
  primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7] }])

private theorem prime_18913 : Nat.Prime 18913 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 197] }])

private theorem prime_20681 : Nat.Prime 20681 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 47] }])

private theorem prime_25657 : Nat.Prime 25657 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1069] }]) [prime_1069]

private theorem prime_26209 : Nat.Prime 26209 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 13] }])

private theorem prime_32779 : Nat.Prime 32779 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 607] }])

private theorem prime_40763 : Nat.Prime 40763 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 89, 229] }])

private theorem prime_65701 : Nat.Prime 65701 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 73] }])

private theorem prime_115471 : Nat.Prime 115471 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1283] }]) [prime_1283]

private theorem prime_166667 : Nat.Prime 166667 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 167, 499] }])

private theorem prime_174017 : Nat.Prime 174017 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 2719] }]) [prime_2719]

private theorem prime_192631 : Nat.Prime 192631 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 6421] }]) [prime_6421]

private theorem prime_239851 : Nat.Prime 239851 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 41] }])

private theorem prime_265157 : Nat.Prime 265157 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 151, 439] }])

private theorem prime_1077697 : Nat.Prime 1077697 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1871] }]) [prime_1871]

private theorem prime_1786469 : Nat.Prime 1786469 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 14407] }]) [prime_14407]

private theorem prime_3572939 : Nat.Prime 3572939 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1786469] }]) [prime_1786469]

private theorem prime_4318891 : Nat.Prime 4318891 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 7577] }]) [prime_7577]

private theorem prime_4623217 : Nat.Prime 4623217 := by
  primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 13, 31, 239] }])

private theorem prime_5220511 : Nat.Prime 5220511 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 174017] }]) [prime_174017]

private theorem prime_5548607 : Nat.Prime 5548607 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 251, 1579] }]) [prime_1579]

private theorem prime_6363769 : Nat.Prime 6363769 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 265157] }]) [prime_265157]

private theorem prime_8541289 : Nat.Prime 8541289 := by
  primality (cert := .witnesses [.lucas { root := 43, primeFactors := [2, 3, 7, 269] }])

private theorem prime_15924371 : Nat.Prime 15924371 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 20681] }]) [prime_20681]

private theorem prime_42393521 : Nat.Prime 42393521 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 40763] }]) [prime_40763]

private theorem prime_149855393 : Nat.Prime 149855393 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1307, 3583] }]) [prime_1307, prime_3583]

private theorem prime_244138709 : Nat.Prime 244138709 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 5548607] }]) [prime_5548607]

private theorem prime_299710787 : Nat.Prime 299710787 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 149855393] }]) [prime_149855393]

private theorem prime_594085421 : Nat.Prime 594085421 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 43, 331, 2087] }]) [prime_2087]

private theorem prime_777448979 : Nat.Prime 777448979 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 73, 1301, 4093] }]) [prime_1301, prime_4093]

private theorem prime_2712263549 : Nat.Prime 2712263549 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 157, 4318891] }]) [prime_4318891]

private theorem prime_2929664509 : Nat.Prime 2929664509 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 244138709] }]) [prime_244138709]

private theorem prime_13994081623 : Nat.Prime 13994081623 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 777448979] }]) [prime_777448979]

private theorem prime_103100510729 : Nat.Prime 103100510729 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 43, 299710787] }]) [prime_299710787]

private theorem prime_37379684141669 : Nat.Prime 37379684141669 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 389, 18913, 115471] }]) [prime_18913, prime_115471]

private theorem prime_566251415628539 : Nat.Prime 566251415628539 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 241, 401, 2929664509] }]) [prime_2929664509]

private theorem prime_100000000000000003 : Nat.Prime 100000000000000003 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 61, 65701, 594085421] }]) [prime_65701, prime_594085421]

private theorem prime_181818181818181813 : Nat.Prime 181818181818181813 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 192631, 2712263549] }]) [prime_192631, prime_2712263549]

private theorem prime_399999999999999979 : Nat.Prime 399999999999999979 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 211, 239851, 6363769] }]) [prime_239851, prime_6363769]

private theorem prime_1000000000000000009 : Nat.Prime 1000000000000000009 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 97, 26209, 32779, 166667] }]) [prime_26209, prime_32779, prime_166667]

private theorem prime_3999999999999998803 : Nat.Prime 3999999999999998803 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 229, 8147, 8429, 42393521] }]) [prime_8147, prime_8429, prime_42393521]

private theorem prime_3999999999999999349 : Nat.Prime 3999999999999999349 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 31, 61, 283, 491, 5220511] }]) [prime_5220511]

private theorem prime_3999999999999999497 : Nat.Prime 3999999999999999497 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 883, 566251415628539] }]) [prime_566251415628539]

private theorem prime_3999999999999999691 : Nat.Prime 3999999999999999691 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 41, 37379684141669] }]) [prime_37379684141669]

private theorem prime_3999999999999999761 : Nat.Prime 3999999999999999761 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 3572939, 13994081623] }]) [prime_3572939, prime_13994081623]

private theorem prime_3999999999999999791 : Nat.Prime 3999999999999999791 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 399999999999999979] }]) [prime_399999999999999979]

private theorem prime_3999999999999999883 : Nat.Prime 3999999999999999883 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 157, 547, 25657, 15924371] }]) [prime_25657, prime_15924371]

private theorem prime_3999999999999999887 : Nat.Prime 3999999999999999887 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 181818181818181813] }]) [prime_181818181818181813]

private theorem prime_4000000000000000037 : Nat.Prime 4000000000000000037 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1000000000000000009] }]) [prime_1000000000000000009]

private theorem prime_4000000000000000049 : Nat.Prime 4000000000000000049 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 487, 4623217, 8541289] }]) [prime_4623217, prime_8541289]

private theorem prime_4000000000000000069 : Nat.Prime 4000000000000000069 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1077697, 103100510729] }]) [prime_1077697, prime_103100510729]

private theorem prime_4000000000000000121 : Nat.Prime 4000000000000000121 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 100000000000000003] }]) [prime_100000000000000003]

end PostBoundaryCertificates

open PostBoundaryCertificates

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_goldbach_finite_post_boundary_prime_block :
    ∀ j : ℕ, 1 ≤ j → j ≤ 64 → let n : ℕ := 4000000000000000000 + 2*j; ∃ p ∈ ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,67,71,127,131,137,139,149,151,163,181,211,227,239,251,313,317,337,367,379,509,769,1213} : Finset ℕ), Nat.Prime p ∧ p < n ∧ Nat.Prime (n-p) := by
  intro j hj hJ
  interval_cases j
  · exact ⟨211, by decide, by decide, by decide, prime_3999999999999999791⟩
  · exact ⟨313, by decide, by decide, by decide, prime_3999999999999999691⟩
  · exact ⟨509, by decide, by decide, by decide, prime_3999999999999999497⟩
  · exact ⟨317, by decide, by decide, by decide, prime_3999999999999999691⟩
  · exact ⟨127, by decide, by decide, by decide, prime_3999999999999999883⟩
  · exact ⟨251, by decide, by decide, by decide, prime_3999999999999999761⟩
  · exact ⟨127, by decide, by decide, by decide, prime_3999999999999999887⟩
  · exact ⟨1213, by decide, by decide, by decide, prime_3999999999999998803⟩
  · exact ⟨131, by decide, by decide, by decide, prime_3999999999999999887⟩
  · exact ⟨137, by decide, by decide, by decide, prime_3999999999999999883⟩
  · exact ⟨139, by decide, by decide, by decide, prime_3999999999999999883⟩
  · exact ⟨137, by decide, by decide, by decide, prime_3999999999999999887⟩
  · exact ⟨139, by decide, by decide, by decide, prime_3999999999999999887⟩
  · exact ⟨337, by decide, by decide, by decide, prime_3999999999999999691⟩
  · exact ⟨239, by decide, by decide, by decide, prime_3999999999999999791⟩
  · exact ⟨149, by decide, by decide, by decide, prime_3999999999999999883⟩
  · exact ⟨151, by decide, by decide, by decide, prime_3999999999999999883⟩
  · exact ⟨149, by decide, by decide, by decide, prime_3999999999999999887⟩
  · exact ⟨151, by decide, by decide, by decide, prime_3999999999999999887⟩
  · exact ⟨3, by decide, by decide, by decide, prime_4000000000000000037⟩
  · exact ⟨5, by decide, by decide, by decide, prime_4000000000000000037⟩
  · exact ⟨7, by decide, by decide, by decide, prime_4000000000000000037⟩
  · exact ⟨163, by decide, by decide, by decide, prime_3999999999999999883⟩
  · exact ⟨11, by decide, by decide, by decide, prime_4000000000000000037⟩
  · exact ⟨13, by decide, by decide, by decide, prime_4000000000000000037⟩
  · exact ⟨3, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨5, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨7, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨367, by decide, by decide, by decide, prime_3999999999999999691⟩
  · exact ⟨11, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨13, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨181, by decide, by decide, by decide, prime_3999999999999999883⟩
  · exact ⟨17, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨19, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨379, by decide, by decide, by decide, prime_3999999999999999691⟩
  · exact ⟨3, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨5, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨7, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨29, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨11, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨13, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨47, by decide, by decide, by decide, prime_4000000000000000037⟩
  · exact ⟨17, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨19, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨41, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨23, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨211, by decide, by decide, by decide, prime_3999999999999999883⟩
  · exact ⟨47, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨29, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨31, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨53, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨67, by decide, by decide, by decide, prime_4000000000000000037⟩
  · exact ⟨37, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨59, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨41, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨43, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨227, by decide, by decide, by decide, prime_3999999999999999887⟩
  · exact ⟨47, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨769, by decide, by decide, by decide, prime_3999999999999999349⟩
  · exact ⟨71, by decide, by decide, by decide, prime_4000000000000000049⟩
  · exact ⟨53, by decide, by decide, by decide, prime_4000000000000000069⟩
  · exact ⟨3, by decide, by decide, by decide, prime_4000000000000000121⟩
  · exact ⟨5, by decide, by decide, by decide, prime_4000000000000000121⟩
  · exact ⟨7, by decide, by decide, by decide, prime_4000000000000000121⟩
