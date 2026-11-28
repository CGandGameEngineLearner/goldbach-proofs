import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace ChenCubicResidues

/-- A witness (a,b,u,v) for each soluble class modulo 91; the entries
for classes congruent to 6 modulo 7 are unused. -/
private def witnesses : List (ℕ × ℕ × ℕ × ℕ) := [
  (1, 90, 1, 4), (6, 86, 3, 2), (1, 1, 1, 1), (8, 86, 1, 2), (22, 73, 1, 2), (6, 90, 3, 4),
  (0, 0, 0, 0), (6, 1, 3, 1), (20, 79, 3, 1), (1, 8, 1, 2), (15, 86, 1, 2), (29, 73, 1, 2),
  (20, 83, 3, 7), (0, 0, 0, 0), (6, 8, 3, 2), (20, 86, 3, 2), (8, 8, 1, 2), (22, 86, 1, 2),
  (36, 73, 1, 2), (1, 18, 1, 7), (0, 0, 0, 0), (20, 1, 3, 1), (27, 86, 3, 2), (15, 8, 1, 2),
  (6, 18, 3, 7), (43, 73, 1, 2), (1, 25, 1, 4), (0, 0, 0, 0), (1, 27, 1, 1), (34, 86, 3, 2),
  (22, 8, 1, 2), (6, 25, 3, 4), (1, 31, 1, 7), (6, 27, 3, 1), (0, 0, 0, 0), (1, 34, 1, 2),
  (41, 86, 3, 2), (6, 31, 3, 7), (20, 18, 3, 7), (1, 38, 1, 4), (6, 34, 3, 2), (0, 0, 0, 0),
  (8, 34, 1, 2), (48, 86, 3, 2), (6, 38, 3, 4), (1, 44, 1, 7), (8, 38, 1, 4), (20, 27, 3, 1),
  (0, 0, 0, 0), (15, 34, 1, 2), (6, 44, 3, 7), (20, 31, 3, 7), (1, 51, 1, 4), (15, 38, 1, 4),
  (1, 53, 1, 1), (0, 0, 0, 0), (22, 34, 1, 2), (6, 51, 3, 4), (1, 57, 1, 7), (6, 53, 3, 1),
  (22, 38, 1, 4), (1, 60, 1, 2), (0, 0, 0, 0), (6, 57, 3, 7), (20, 44, 3, 7), (1, 64, 1, 4),
  (6, 60, 3, 2), (1, 66, 1, 1), (8, 60, 1, 2), (0, 0, 0, 0), (6, 64, 3, 4), (20, 51, 3, 4),
  (6, 66, 3, 1), (20, 53, 3, 1), (1, 73, 1, 2), (15, 60, 1, 2), (0, 0, 0, 0), (20, 57, 3, 7),
  (27, 51, 3, 4), (6, 73, 3, 2), (1, 79, 1, 1), (8, 73, 1, 2), (22, 60, 1, 2), (0, 0, 0, 0),
  (1, 83, 1, 7), (6, 79, 3, 1), (20, 66, 3, 1), (1, 86, 1, 2), (15, 73, 1, 2), (6, 83, 3, 7),
  (0, 0, 0, 0)]

private theorem witnesses_correct : ∀ r : Fin 91, r.val % 7 ≠ 6 →
    let (a,b,u,v) := witnesses.getD r.val (0,0,0,0)
    a < 91 ∧ b < 91 ∧ (a*(a+2)*b*(b+2)).Coprime 91 ∧
      (a+b)%91 = r.val ∧ u^3%7 = a%7 ∧ v^3%13 = b%13 := by
  set_option maxRecDepth 10000 in decide

private theorem obstruction (a b u : ℕ) (h : (a*(a+2)*b*(b+2)).Coprime 91)
    (hc : u^3%7 = a%7) : (a+b)%7 ≠ 6 := by
  intro hs
  have table : ∀ i j k : Fin 7, k.val^3%7 = i.val → (i.val+j.val)%7=6 →
      (i.val*(i.val+2)*j.val*(j.val+2))%7=0 := by decide
  have ha := Nat.mod_modEq a 7
  have hb := Nat.mod_modEq b 7
  have hz := table ⟨a%7, by omega⟩ ⟨b%7, by omega⟩ ⟨u%7, by omega⟩
    ((Nat.pow_mod u 3 7).symm.trans hc) (Eq.trans (ha.add hb) hs)
  have heq := ((ha.mul (ha.add_right 2)).mul hb).mul (hb.add_right 2)
  have hzero : (a*(a+2)*b*(b+2))%7=0 := Eq.trans (Eq.symm heq) hz
  have h7 : (a*(a+2)*b*(b+2)).Coprime 7 := h.of_dvd_right (by decide : 7 ∣ 91)
  exact (show Nat.Prime 7 by decide).coprime_iff_not_dvd.mp h7.symm (Nat.dvd_of_mod_eq_zero hzero)

end ChenCubicResidues

theorem Conjectures.Cuts.Task200cb2ac309d434301f1b1c2 : (have x1 : Finset ℕ := {(4 : ℕ), (10 : ℕ), (16 : ℕ), (22 : ℕ), (28 : ℕ), (40 : ℕ)}; ∀ (x2 : ℕ), (x2 % (6 : ℕ) = (4 : ℕ) ∧ ∃ (x3 : ℕ) (x4 : ℕ), x3 < (91 : ℕ) ∧ x4 < (91 : ℕ) ∧ (x3 * (x3 + (2 : ℕ)) * x4 * (x4 + (2 : ℕ))).Coprime (91 : ℕ) ∧ (x3 + x4) % (91 : ℕ) = x2 % (91 : ℕ) ∧ (∃ (x5 : ℕ), x5 ^ (3 : ℕ) % (7 : ℕ) = x3 % (7 : ℕ)) ∧ ∃ (x5 : ℕ), x5 ^ (3 : ℕ) % (13 : ℕ) = x4 % (13 : ℕ)) ↔ x2 % (42 : ℕ) ∈ x1) := by
  dsimp only
  intro n
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h6,a,b,_,_,hc,hs,⟨u,hu⟩,_⟩
    have hm : (a+b)%7 = n%7 := Nat.ModEq.of_dvd (by decide : 7 ∣ 91) hs
    have h7 := ChenCubicResidues.obstruction a b u hc hu
    omega
  · intro hr
    have h6 : n%6=4 := by omega
    have h7 : (n%91)%7 ≠ 6 := by omega
    refine ⟨h6, ?_⟩
    let r : Fin 91 := ⟨n%91, by omega⟩
    have H := ChenCubicResidues.witnesses_correct r h7
    rcases hw : ChenCubicResidues.witnesses.getD r.val (0,0,0,0) with ⟨a,b,u,v⟩
    rw [hw] at H
    exact ⟨a,b,H.1,H.2.1,H.2.2.1,H.2.2.2.1,⟨u,H.2.2.2.2.1⟩,⟨v,H.2.2.2.2.2⟩⟩
