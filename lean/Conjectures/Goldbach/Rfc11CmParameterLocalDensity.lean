import Mathlib

/-! The affine CM parameter permutes the residues modulo 105. This
reduces every block to the same finite wheel, indexed by the target
residue. All finite checks are evaluated by the Lean kernel. -/

namespace Conjectures.Goldbach.Rfc11DensityProof

private def good (n r : ℕ) : Prop :=
  (r+104).Coprime 105 ∧ ((n+(106-r))%105).Coprime 105

private instance (n r : ℕ) : Decidable (good n r) := by unfold good;infer_instance

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
private theorem wheel : ∀ n : Fin 105,
    15 ≤ ((Finset.range 105).filter (fun r => good n.val r)).card := by
  decide

private def parameter (s a i : ℕ) := 2^s*(2*(a+i)+1)

private theorem permutes (s a : ℕ) :
    Set.InjOn (fun i => parameter s a i % 105) (↑(Finset.range 105) : Set ℕ) := by
  intro i hi j hj eqn
  have ii : i<105 := Finset.mem_range.mp hi
  have jj : j<105 := Finset.mem_range.mp hj
  have h := (ZMod.natCast_eq_natCast_iff' _ _ 105).mpr eqn
  unfold parameter at h
  push_cast at h
  have unit : IsUnit (2:ZMod 105) := (ZMod.isUnit_iff_coprime 2 105).mpr (by decide)
  have cancel := (unit.pow s).mul_right_inj.mp h
  have pair := unit.mul_right_inj.mp (add_right_cancel cancel)
  have residues := (ZMod.natCast_eq_natCast_iff' i j 105).mp (add_left_cancel pair)
  simpa only [Nat.mod_eq_of_lt ii,Nat.mod_eq_of_lt jj] using residues

private theorem reduce (n x : ℕ) :
    ((x+104).Coprime 105 ∧ ((n+1+105-(x%105))%105).Coprime 105) ↔ good (n%105) (x%105) := by
  have small : x%105<105 := Nat.mod_lt _ (by decide)
  have first : (x+104).Coprime 105 ↔ (x%105+104).Coprime 105 := by
    rw [←ZMod.isUnit_iff_coprime,←ZMod.isUnit_iff_coprime]
    push_cast
    rw [ZMod.natCast_mod]
  have second : (n+1+105-x%105)%105=(n%105+(106-x%105))%105 := by
    rw [show n+1+105-x%105=n+(106-x%105) by omega,Nat.mod_add_mod]
  unfold good
  rw [first,second]

theorem density (n s a : ℕ) :
    15 ≤ ((Finset.range 105).filter (fun i =>
      let x := parameter s a i
      (x+104).Coprime 105 ∧ ((n+1+105-(x%105))%105).Coprime 105)).card := by
  let I := Finset.range 105
  let f (i : ℕ) := parameter s a i%105
  let P (r : ℕ) := good (n%105) r
  have inj : Set.InjOn f (↑I : Set ℕ) := permutes s a
  have onto : I.image f=I := Finset.eq_of_subset_of_card_le (by
    intro r hr
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by decide))) (by rw [Finset.card_image_of_injOn inj])
  change 15≤(I.filter _).card
  have filtered : I.filter (fun i => ((parameter s a i+104).Coprime 105 ∧
      ((n+1+105-(parameter s a i%105))%105).Coprime 105)) = I.filter (fun i => P (f i)) := by
    apply Finset.filter_congr
    intro i _
    exact reduce n (parameter s a i)
  rw [filtered]
  have card : ((I.filter (fun i => P (f i))).image f).card=(I.filter (fun i => P (f i))).card :=
    Finset.card_image_of_injOn (inj.mono (Finset.filter_subset _ _))
  rw [←card,←Finset.filter_image,onto]
  exact wheel ⟨n%105,Nat.mod_lt _ (by decide)⟩

end Conjectures.Goldbach.Rfc11DensityProof

theorem Conjectures.Goldbach.Rfc11CmParameterLocalDensity :
    ∀ n s a : ℕ, 2∣n → 1 ≤ s → 15 ≤ ((Finset.range 105).filter (fun i => let x := 2^s*(2*(a+i)+1); Nat.Coprime (x+104) 105 ∧ Nat.Coprime ((n+1+105-(x%105))%105) 105)).card := by
  intro n s a _ _
  exact Rfc11DensityProof.density n s a
