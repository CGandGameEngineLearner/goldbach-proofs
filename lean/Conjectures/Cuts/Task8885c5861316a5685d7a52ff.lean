import Mathlib

open Finset

namespace ShiftUnion

theorem shift_range {X n e : ℕ} (hX : 16 ≤ X) (hn : n ∈ Finset.Ico X (2*X))
    (he : e ∈ Finset.Icc 1 (Nat.log 2 X / 2)) (en : Even n) :
    n-2^e ∈ Finset.Icc 4 (2*X) ∧ Even (n-2^e) ∧ 2^e ≤ n := by
  obtain ⟨lower,upper⟩ := Finset.mem_Ico.mp hn
  obtain ⟨ep,ec⟩ := Finset.mem_Icc.mp he
  have lg : 4 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by decide) hX
  have far : e+1 ≤ Nat.log 2 X := by omega
  have twice : 2^e*2 ≤ X := by
    rw [← Nat.pow_succ]
    exact (Nat.pow_le_pow_right (by decide : 0<2) far).trans
      (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
  have parity : Even (2^e) := by
    obtain ⟨f,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    exact ⟨2^f, by rw [pow_succ];omega⟩
  rw [Nat.even_iff] at en parity ⊢
  exact ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega,by omega⟩

open Finset
theorem count (R:ℕ→ℕ) (X:ℕ) (hX:16≤X) :
    ((Ico X (2*X)).filter (fun n=>Even n ∧ 0<((Icc 1 (Nat.log 2 X/2)).filter (fun e=>R (n-2^e)=0)).card)).card ≤
      (Nat.log 2 X/2)*((Icc 4 (2*X)).filter (fun m=>Even m ∧ R m=0)).card := by
  classical
  let E:=Icc 1 (Nat.log 2 X/2)
  let B:=(Icc 4 (2*X)).filter (fun m=>Even m ∧ R m=0)
  let S:=(Ico X (2*X)).filter (fun n=>Even n ∧ 0<(E.filter (fun e=>R (n-2^e)=0)).card)
  let row:=fun e:ℕ=>B.image (fun m=>m+2^e)
  have cover:S⊆E.biUnion row:=by
    intro n hn
    obtain ⟨nx,evenN,pos⟩:=mem_filter.mp hn
    obtain ⟨e,hit⟩:=card_pos.mp pos
    obtain ⟨member,zero⟩:=mem_filter.mp hit
    obtain ⟨rangeM,evenM,fit⟩:=shift_range hX nx member evenN
    have bad:(n-2^e)∈B:=mem_filter.mpr ⟨rangeM,evenM,zero⟩
    exact mem_biUnion.mpr ⟨e,member,mem_image.mpr ⟨n-2^e,bad,Nat.sub_add_cancel fit⟩⟩
  apply (card_le_card cover).trans (card_biUnion_le.trans ?_)
  calc
    _ ≤ ∑_e∈E,B.card:=sum_le_sum (fun e _=>Finset.card_image_le)
    _ = _:=by simp [E,B]

end ShiftUnion

theorem Conjectures.Cuts.Task8885c5861316a5685d7a52ff : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∀ (x2 : ℕ),   (16 : ℕ) ≤ x2 →     have x4 : ℕ := Nat.log (2 : ℕ) x2 / (2 : ℕ);     have x5 : Finset ℕ := {x5 ∈ Finset.Ico x2 ((2 : ℕ) * x2) | Even x5 ∧ (0 : ℕ) < {x6 ∈ Finset.Icc (1 : ℕ) x4 | x1 (x5 - (2 : ℕ) ^ x6) = (0 : ℕ)}.card};     x5.card ≤ x4 * {x6 ∈ Finset.Icc (4 : ℕ) ((2 : ℕ) * x2) | Even x6 ∧ x1 x6 = (0 : ℕ)}.card) := by
  classical
  let R := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
  exact fun X hX => ShiftUnion.count R X hX
