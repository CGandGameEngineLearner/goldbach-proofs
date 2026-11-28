import Mathlib

/-! Subtract the mean of each class modulo p, then reassemble its p residue classes modulo p². -/

namespace LayerMass

open Finset

noncomputable def mass (w : ℕ → ℝ) (X d c : ℕ) : ℝ :=
  ∑ m ∈ (range X).filter (fun m : ℕ => m % d = c), w m

theorem row_mass (w : ℕ → ℝ) (X p c : ℕ) (hp : 0 < p) (hc : c < p) :
    (∑ j ∈ range p, mass w X (p^2) (c+p*j)) = mass w X p c := by
  let row := (range X).filter (fun m : ℕ => m % p=c)
  let digit (m : ℕ) := (m % p^2)/p
  have hmap (m : ℕ) (_ : m ∈ row) : digit m ∈ range p := by
    apply mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    simpa [pow_two] using Nat.mod_lt m (pow_pos hp 2)
  have hmod (m : ℕ) : m % p^2 % p = m % p := by simp [pow_two]
  have fiber (j : ℕ) :
      (range X).filter (fun m : ℕ => m % p^2=c+p*j) = row.filter (fun m => digit m=j) := by
    ext m
    simp only [row, mem_filter, mem_range]
    constructor
    · rintro ⟨hm,he⟩
      have h₁ := congrArg (fun k : ℕ => k % p) he
      have h₂ := congrArg (fun k : ℕ => k/p) he
      exact ⟨⟨hm, by simpa only [hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc] using h₁⟩,
        by simpa only [digit, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hc, zero_add] using h₂⟩
    · rintro ⟨⟨hm,hr⟩,hj⟩
      refine ⟨hm, ?_⟩
      have hx := Nat.mod_add_div (m % p^2) p
      change (m % p^2)/p = j at hj
      simpa only [hmod, hr, hj] using hx.symm
  calc
    _ = ∑ j ∈ range p, ∑ m ∈ row.filter (fun m => digit m=j), w m := by
      apply sum_congr rfl
      intro j _
      unfold mass
      rw [fiber]
    _ = _ := sum_fiberwise_of_maps_to hmap w

end LayerMass

namespace LayerVariance
open Finset

theorem centered (p : ℕ) (hp : 0 < p) (f : ℕ → ℝ) :
    (∑ j ∈ range p, (f j - (∑ k ∈ range p, f k)/(p:ℝ))^2) =
      (∑ j ∈ range p, (f j)^2) - (∑ k ∈ range p, f k)^2/(p:ℝ) := by
  let a := (∑ k ∈ range p, f k)/(p:ℝ)
  have expand (x : ℝ) : (x-a)^2 = x^2 - (2*a)*x + a^2 := by ring
  change (∑ j ∈ range p, (f j-a)^2) = _
  simp only [expand, sum_add_distrib, sum_sub_distrib, ←mul_sum, sum_const, card_range, nsmul_eq_mul]
  dsimp [a]
  field_simp [Nat.cast_ne_zero.mpr hp.ne']
  ring

end LayerVariance

namespace LayerChart
open Finset
private theorem residue_rows (p : ℕ) (hp : 0 < p) (G : ℕ → ℝ) :
    (∑ r ∈ range (p^2), G r) = ∑ c ∈ range p, ∑ j ∈ range p, G (c+p*j) := by
  let decode (v : ℕ × ℕ) := v.1 + p*v.2
  let encode (r : ℕ) := (r % p, r/p)
  have section_prop (r : ℕ) : decode (encode r) = r := Nat.mod_add_div r p
  have retract (v : ℕ × ℕ) (hv : v ∈ (range p ×ˢ range p)) : encode (decode v) = v := by
    have h := mem_range.mp (mem_product.mp hv).1
    simp [encode, decode, Nat.add_mul_div_left _ _ hp, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
  have mapin (r : ℕ) (hr : r ∈ range (p^2)) : encode r ∈ range p ×ˢ range p := by
    exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hp), mem_range.mpr
      ((Nat.div_lt_iff_lt_mul hp).mpr (by simpa [pow_two] using mem_range.mp hr))⟩
  calc
    _ = ∑ v ∈ range p ×ˢ range p, G (decode v) := by
      apply sum_bij (fun r _ => encode r) mapin
      · intro r _ s _ he
        simpa only [section_prop] using congrArg decode he
      · intro v hv
        refine ⟨decode v, mem_range.mpr ?_, retract v hv⟩
        have h0 := mem_range.mp (mem_product.mp hv).1
        have h1 := mem_range.mp (mem_product.mp hv).2
        change v.1+p*v.2 < p^2
        nlinarith [Nat.mul_le_mul_left p (show v.2+1 ≤ p by omega)]
      · intro r _
        rw [section_prop]
    _ = _ := sum_product _ _ _


end LayerChart

theorem Conjectures.Cuts.Task400f181c9c186da30062725c : (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) =>   have x4 : ℕ → ℕ → ℝ := fun (x4 x5 : ℕ) => ∑ x6 ∈ Finset.range x2 with x6 % x3 ^ (2 : ℕ) = x4 + x3 * x5, x1 x6;   ∑ x5 ∈ Finset.range x3, ∑ x6 ∈ Finset.range x3, (x4 x5 x6 - (∑ x7 ∈ Finset.range x3, x4 x5 x7) / ↑x3) ^ (2 : ℕ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.range x4, (∑ x6 ∈ Finset.range x3 with x6 % x4 = x5, x2 x6) ^ (2 : ℕ); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ), (0 : ℕ) < x5 → x1 x3 x4 x5 = x2 x3 x4 (x5 ^ (2 : ℕ)) - x2 x3 x4 x5 / ↑x5) := by
  classical
  intro V A w X p hp
  let f (c j : ℕ) := LayerMass.mass w X (p^2) (c+p*j)
  change (∑ c ∈ Finset.range p, ∑ j ∈ Finset.range p,
      (f c j - (∑ k ∈ Finset.range p, f c k)/(p:ℝ))^2) =
    (∑ r ∈ Finset.range (p^2), (LayerMass.mass w X (p^2) r)^2) -
      (∑ c ∈ Finset.range p, (LayerMass.mass w X p c)^2)/(p:ℝ)
  calc
    _ = ∑ c ∈ Finset.range p,
          ((∑ j ∈ Finset.range p, (f c j)^2) - (LayerMass.mass w X p c)^2/(p:ℝ)) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [LayerVariance.centered p hp (f c)]
      have row : (∑ k ∈ Finset.range p, f c k) = LayerMass.mass w X p c :=
        LayerMass.row_mass w X p c hp (Finset.mem_range.mp hc)
      rw [row]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, LayerChart.residue_rows p hp]
