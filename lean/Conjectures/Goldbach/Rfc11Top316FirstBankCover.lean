import Mathlib

/-! Exact coverage of the first 40 offsets in the RFC1.1 anchor table.
The square-root bound below concerns the small difference t - 2*i. -/

namespace GoldbachFirstBank

private def offsets : List ℕ := ([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ).take 40
private def misses : List ℕ := [7564, 7909, 11134, 11329, 11989, 12154]

/-- Precomputed value of 256 factorial for the closed coprimality checks. -/
private def divisorProduct : ℕ := 857817775342842654119082271681232625157781520279485619859655650377269452553147589377440291360451408450375885342336584306157196834693696475322289288497426025679637332563368786442675207626794560187968867971521143307702077526646451464709187326100832876325702818980773671781454170250523018608495319068138257481070252817559459476987034665712738139286205234756808218860701203611083152093501947437109101726968262861606263662435022840944191408424615936000000000000000000000000000000000000000000000000000000000000000

private theorem divisorProduct_eq : divisorProduct = Nat.factorial 256 := by decide +kernel

private def primeTest (m : ℕ) : Bool :=
  if m ≤ 256 then decide m.Prime else decide (m.Coprime divisorProduct)

private theorem primeTest_spec {m : ℕ} (hcap : m < 66049) :
    primeTest m = true ↔ m.Prime := by
  by_cases hs : m ≤ 256
  · simp [primeTest, hs]
  simp only [primeTest, ite_eq_right hs, decide_eq_true_eq, divisorProduct_eq]
  constructor
  · intro hcop
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega, ?_⟩
    intro d hd hds hdm
    have hroot : Nat.sqrt m < 257 := Nat.sqrt_lt'.mpr (by norm_num; exact hcap)
    have hdprod : d ∣ Nat.factorial 256 := Nat.dvd_factorial (by omega) (by omega)
    have hdgcd := Nat.dvd_gcd hdm hdprod
    rw [hcop.gcd_eq_one] at hdgcd
    have := Nat.dvd_one.mp hdgcd
    omega
  · intro hp
    exact hp.coprime_factorial_of_lt (by omega)

private theorem offsets_small : offsets.all (fun t => decide (t < 66049)) = true := by decide

private def covered (i : ℕ) : Bool := offsets.any fun t => primeTest (t - 2*i)
private def agrees (i : ℕ) : Bool := covered i == !(decide (i ∈ misses))

private theorem covered_spec (i : ℕ) : covered i = true ↔ ∃ t ∈ offsets, (t-2*i).Prime := by
  unfold covered
  rw [List.any_eq_true]
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  have hbound : t < 66049 := of_decide_eq_true ((List.all_eq_true.mp offsets_small) t ht)
  exact primeTest_spec ((Nat.sub_le t (2*i)).trans_lt hbound)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem blocks : ∀ b : Fin 96,
    (List.range 128).all (fun j => agrees (1+128*b.val+j)) = true := by
  decide +kernel

theorem coverage (i : ℕ) (hi : 1 ≤ i) (hmax : i ≤ 12288) :
    (∃ t ∈ offsets, (t-2*i).Prime) ↔ i ∉ misses := by
  let b : Fin 96 := ⟨(i-1)/128, by omega⟩
  have hh := (List.all_eq_true.mp (blocks b)) ((i-1)%128)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  change agrees (1+128*((i-1)/128)+(i-1)%128) = true at hh
  rw [show 1+128*((i-1)/128)+(i-1)%128=i by omega] at hh
  have he : covered i = !(decide (i ∈ misses)) := beq_iff_eq.mp hh
  rw [← covered_spec, he]
  simp

end GoldbachFirstBank

theorem Conjectures.Goldbach.Rfc11Top316FirstBankCover :
    let offsets := ([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ).take 40; ∀ i : ℕ, 1 ≤ i → i ≤ 12288 → ((∃ t ∈ offsets, Nat.Prime (t-2*i)) ↔ i ∉ ([7564,7909,11134,11329,11989,12154] : List ℕ)) := by
  exact GoldbachFirstBank.coverage
