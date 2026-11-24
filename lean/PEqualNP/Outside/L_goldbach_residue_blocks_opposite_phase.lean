import Mathlib

/-!
# L-goldbach-residue-blocks-opposite-phase

Adding the complementary residue `q - a` and then restoring `a` returns the
original residue class: the shift by `q` is invisible modulo `q`.
-/

theorem PEqualNP.Outside.L_goldbach_residue_blocks_opposite_phase :
    ∀ (q a n : ℕ), 0<q → a<q → ((n+q-a) % q+a) % q=n % q := by
  intro q a n hq0 ha
  have hq0mod : q ≡ 0 [MOD q] := (dvd_refl q).modEq_zero_nat
  have h1 : (n + q - a) % q + a ≡ (n + q - a) + a [MOD q] :=
    (Nat.mod_modEq (n + q - a) q).add_right a
  have h2 : (n + q - a) + a = n + q :=
    Nat.sub_add_cancel (le_trans ha.le (Nat.le_add_left q n))
  have h3 : n + q ≡ n [MOD q] :=
    ((Nat.ModEq.refl n).add hq0mod).trans rfl
  have hfin : ((n + q - a) % q + a) ≡ n [MOD q] := by
    refine h1.trans ?_
    rw [h2]
    exact h3
  exact hfin
