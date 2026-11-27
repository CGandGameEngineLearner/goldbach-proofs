import Mathlib

/-!
E05 in `research/checkpoint/哥德巴赫任务拆分4.md`.
The affine parameter map permutes the 105 residues. The residue count is
then checked exhaustively in the kernel for each possible target residue.
-/

namespace Conjectures.Goldbach.Rfc11CmParameterLocalDensityAux

private def survives (n x : ℕ) : Prop :=
  Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-x)%105) 105

private instance (n x : ℕ) : Decidable (survives n x) := by
  unfold survives
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem residue_count : ∀ n : Fin 105,
    15 ≤ ((Finset.range 105).filter (survives (n:ℕ))).card := by
  decide

private theorem survives_target_mod (n x : ℕ) (hx : x < 105) :
    survives n x ↔ survives (n%105) x := by
  have h (m : ℕ) : m+1+105-x = m+(106-x) := by omega
  unfold survives
  rw [h n, h (n%105), Nat.mod_add_mod]

private theorem coprime_add104_mod (x : ℕ) :
    Nat.Coprime (x+104) 105 ↔ Nat.Coprime (x%105+104) 105 := by
  have h := ((Nat.mod_modEq x 105).symm.add_right 104).gcd_eq
  simp only [Nat.coprime_iff_gcd_eq_one, h]

/-- The affine parameter map has unit slope modulo 105, so its first
105 values exhaust the complete residue system. -/
private theorem affine_image (s a : ℕ) :
    let f := fun i : ℕ => (2^s*(2*(a+i)+1))%105
    (Finset.range 105).image f = Finset.range 105 ∧
      Set.InjOn f (↑(Finset.range 105) : Set ℕ) := by
  intro f
  have htwo : Nat.Coprime 105 2 := by decide
  have hinj : Set.InjOn f (↑(Finset.range 105) : Set ℕ) := by
    intro i hi j hj hij
    have h₁ := Nat.ModEq.cancel_left_of_coprime (htwo.pow_right s).gcd_eq_one
      (show 2^s*(2*(a+i)+1) ≡ 2^s*(2*(a+j)+1) [MOD 105] from hij)
    have h₂ := Nat.ModEq.add_right_cancel' 1 h₁
    have h₃ := Nat.ModEq.cancel_left_of_coprime htwo.gcd_eq_one h₂
    have h₄ := Nat.ModEq.add_left_cancel' a h₃
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] using h₄
  refine ⟨Finset.eq_of_subset_of_card_le ?_ (Finset.card_image_of_injOn hinj).ge, hinj⟩
  intro r hr
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  exact Finset.mem_range.mpr (Nat.mod_lt _ (by decide))

theorem result (n s a : ℕ) :
    15 ≤ ((Finset.range 105).filter (fun i =>
      let x := 2^s*(2*(a+i)+1)
      Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x%105))%105) 105)).card := by
  let f := fun i : ℕ => (2^s*(2*(a+i)+1))%105
  let R := Finset.range 105
  obtain ⟨himage, hinj⟩ := affine_image s a
  change R.image f = R at himage
  change Set.InjOn f (↑R : Set ℕ) at hinj
  have hcases : ((R.filter (survives n)).card) ≥ 15 := by
    have heq : R.filter (survives n) = R.filter (survives (n%105)) := by
      ext x
      simp only [Finset.mem_filter]
      exact and_congr_right (fun hx => survives_target_mod n x (Finset.mem_range.mp hx))
    rw [heq]
    exact residue_count ⟨n%105, Nat.mod_lt _ (by decide)⟩
  have hfilter : (R.filter (fun i =>
      let x := 2^s*(2*(a+i)+1)
      Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x%105))%105) 105)) =
      R.filter (fun i => survives n (f i)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_filter]
    exact and_congr_right fun _ => and_congr (coprime_add104_mod (2^s*(2*(a+i)+1))) Iff.rfl
  rw [hfilter]
  have hfiltered : (R.filter (fun i => survives n (f i))).image f = R.filter (survives n) := by
    rw [← Finset.filter_image, himage]
  rw [← hfiltered, Finset.card_image_of_injOn (hinj.mono (by
    intro i hi
    exact (Finset.mem_filter.mp hi).1))] at hcases
  exact hcases

end Conjectures.Goldbach.Rfc11CmParameterLocalDensityAux

theorem Conjectures.Goldbach.Rfc11CmParameterLocalDensity :
    ∀ n s a : ℕ, 2∣n → 1 ≤ s →
      15 ≤ ((Finset.range 105).filter (fun i => let x := 2^s*(2*(a+i)+1);
        Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x%105))%105) 105)).card := by
  intro n s a _ _
  exact Conjectures.Goldbach.Rfc11CmParameterLocalDensityAux.result n s a
