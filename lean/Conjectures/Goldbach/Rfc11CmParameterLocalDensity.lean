import Mathlib

open Finset
open scoped Nat

private abbrev compatible105 (n x : ℕ) : Prop :=
  Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x % 105)) % 105) 105

private theorem compatible105_reduce (n x : ℕ) :
    compatible105 n x ↔ compatible105 (n % 105) (x % 105) := by
  let r := x % 105
  have hr : r < 105 := Nat.mod_lt _ (by decide)
  have hx := Nat.mod_add_div x 105
  have hn := Nat.mod_add_div n 105
  have hX : x+104 = (r+104)+(x/105)*105 := by dsimp only [r]; omega
  have hN : n+1+105-r = (n % 105+1+105-r)+(n/105)*105 := by omega
  have hR : r % 105 = r := Nat.mod_eq_of_lt hr
  change (Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-r) % 105) 105) ↔
    (Nat.Coprime (r+104) 105 ∧ Nat.Coprime ((n % 105+1+105-(r % 105)) % 105) 105)
  rw [hR,hX,Nat.coprime_add_mul_right_left,hN]
  simp

private theorem cm_parameter_permutation (a s : ℕ) :
    Set.InjOn (fun i : ℕ => (2^s*(2*(a+i)+1)) % 105) (range 105 : Set ℕ) := by
  intro i hi j hj h
  have h2 : Nat.Coprime 105 2 := by decide
  have hP : Nat.gcd 105 (2^s) = 1 := h2.pow_right s
  have hMod : 2^s*(2*(a+i)+1) ≡ 2^s*(2*(a+j)+1) [MOD 105] := h
  have hOdd := Nat.ModEq.cancel_left_of_coprime hP hMod
  have hEven := Nat.ModEq.add_right_cancel' 1 hOdd
  have hShift := Nat.ModEq.cancel_left_of_coprime h2 hEven
  have hiR := mem_range.mp hi
  have hjR := mem_range.mp hj
  have hEq : i % 105 = j % 105 := Nat.ModEq.add_left_cancel' a hShift
  simpa only [Nat.mod_eq_of_lt hiR,Nat.mod_eq_of_lt hjR] using hEq

private theorem compatible105_residue_table :
    ∀ n : Fin 105, 15 ≤ ((range 105).filter (compatible105 (n:ℕ))).card :=
  by decide +kernel

theorem Conjectures.Goldbach.Rfc11CmParameterLocalDensity :
    (∀ n s a : ℕ, 2∣n → 1 ≤ s → 15 ≤ ((Finset.range 105).filter (fun i => let x := 2^s*(2*(a+i)+1); Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x % 105)) % 105) 105)).card) := by
  intro n s a _ _
  let x := fun i : ℕ => 2^s*(2*(a+i)+1)
  let f := fun i : ℕ => x i % 105
  let S := (range 105).filter (fun i => compatible105 n (x i))
  let T := (range 105).filter (compatible105 (n % 105))
  have hInj : Set.InjOn f (range 105 : Set ℕ) := cm_parameter_permutation a s
  have hRange : (range 105).image f = range 105 := by
    apply eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨i,_,rfl⟩ := mem_image.mp hr
      exact mem_range.mpr (Nat.mod_lt _ (by decide))
    · rw [card_image_of_injOn hInj]
  have hMatch (i : ℕ) : compatible105 n (x i) ↔ compatible105 (n % 105) (f i) :=
    compatible105_reduce n (x i)
  have hImage : S.image f = T := by
    ext r
    constructor
    · intro hr
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      exact mem_filter.mpr
        ⟨mem_range.mpr (Nat.mod_lt _ (by decide)), (hMatch i).mp (mem_filter.mp hi).2⟩
    · intro hr
      obtain ⟨hrRange,hrGood⟩ := mem_filter.mp hr
      have him : r ∈ (range 105).image f := by rwa [hRange]
      obtain ⟨i,hi,hEq⟩ := mem_image.mp him
      refine mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,(hMatch i).mpr ?_⟩,hEq⟩
      rwa [hEq]
  have hSmallInj : Set.InjOn f (S : Set ℕ) := by
    intro i hi j hj he
    exact hInj (mem_filter.mp hi).1 (mem_filter.mp hj).1 he
  change 15 ≤ S.card
  rw [← card_image_of_injOn hSmallInj,hImage]
  exact compatible105_residue_table ⟨n % 105,Nat.mod_lt _ (by decide)⟩
