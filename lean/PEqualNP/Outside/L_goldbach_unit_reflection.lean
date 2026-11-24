import Mathlib

private lemma reflection_cast_sub (q n a : ℕ) (ha : a ≤ q) :
    ((n + q - a : ℕ) : ZMod q) = (n : ZMod q) - (a : ZMod q) := by
  have h1 : n + q - a = n + (q - a) := by omega
  rw [h1, Nat.cast_add, Nat.cast_sub ha, ZMod.natCast_self, zero_sub, sub_eq_add_neg]

private lemma reflection_mem_U_iff (q n a : ℕ) :
    a ∈ (Finset.range q).filter
      (fun a => Nat.Coprime a q ∧ Nat.Coprime (n + q - a) q) ↔
      a < q ∧ IsUnit (a : ZMod q) ∧ IsUnit ((n : ZMod q) - (a : ZMod q)) := by
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, h1, h2⟩
    have ha : a ≤ q := le_of_lt hlt
    refine ⟨hlt, (ZMod.isUnit_iff_coprime a q).2 h1, ?_⟩
    rw [← reflection_cast_sub q n a ha]
    exact (ZMod.isUnit_iff_coprime (n + q - a) q).2 h2
  · rintro ⟨hlt, h1, h2⟩
    have ha : a ≤ q := le_of_lt hlt
    refine ⟨hlt, (ZMod.isUnit_iff_coprime a q).1 h1, ?_⟩
    rw [← reflection_cast_sub q n a ha] at h2
    exact (ZMod.isUnit_iff_coprime (n + q - a) q).1 h2

namespace PEqualNP.Outside

theorem L_goldbach_unit_reflection :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n a, a ∈ U q n → HMod.hMod (n+q-a) q ∈ U q n := by
  dsimp only
  intro q n a ha
  let b := HMod.hMod (n + q - a) q
  have hmem := (reflection_mem_U_iff q n a).mp ha
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le a) hmem.1
  have hb_lt : b < q := by
    dsimp only [b]
    exact Nat.mod_lt (n + q - a) hq
  have hb_cast : (b : ZMod q) = (n : ZMod q) - (a : ZMod q) := by
    calc
      (b : ZMod q) = ((n + q - a : ℕ) : ZMod q) := by
        dsimp only [b]
        simpa only using ZMod.natCast_mod (n + q - a) q
      _ = (n : ZMod q) - (a : ZMod q) :=
        reflection_cast_sub q n a (le_of_lt hmem.1)
  have hb_unit : IsUnit (b : ZMod q) := by
    rw [hb_cast]
    exact hmem.2.2
  have hnb_unit : IsUnit ((n : ZMod q) - (b : ZMod q)) := by
    rw [hb_cast]
    convert hmem.2.1 using 1
    abel
  exact (reflection_mem_U_iff q n b).mpr ⟨hb_lt, hb_unit, hnb_unit⟩

end PEqualNP.Outside
