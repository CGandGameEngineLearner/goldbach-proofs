import Mathlib

theorem Conjectures.Goldbach.BeaumontPrimitiveCycle :
  ∀ m : ℕ, 2 ≤ m → (Nat.Prime m ↔ ∀ a : ZMod m, a ≠ 0 → Function.Surjective (fun k : ZMod m => a*k)) := by
  intro m hm
  constructor
  · intro hp a ha y
    have : Fact (Nat.Prime m) := ⟨hp⟩
    refine ⟨a⁻¹ * y, ?_⟩
    exact mul_inv_cancel_left₀ ha y
  · intro hsurj
    rw [Nat.prime_def_lt]
    refine ⟨hm, fun d hdlt hdvd => ?_⟩
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hd_ne_zero : (d : ZMod m) ≠ 0 := by
      intro hzero
      have hmd : m ∣ d := (ZMod.natCast_eq_zero_iff d m).mp hzero
      have hle : m ≤ d := Nat.le_of_dvd hd_pos hmd
      omega
    obtain ⟨k, hk⟩ := hsurj (d : ZMod m) hd_ne_zero 1
    have hunit : IsUnit (d : ZMod m) :=
      ⟨⟨(d : ZMod m), k, hk, by rw [mul_comm]; exact hk⟩, rfl⟩
    have hcop : d.Coprime m := (ZMod.isUnit_iff_coprime d m).mp hunit
    exact Nat.eq_one_of_dvd_coprimes hcop (dvd_refl d) hdvd
