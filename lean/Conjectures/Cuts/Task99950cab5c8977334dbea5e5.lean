import Mathlib

namespace GoldbachResidueMass

open Finset

theorem squared_residues (f : ℕ → ℝ) (N q : ℕ) (hq : 0 < q) :
    (∑ r ∈ range q, (∑ i ∈ range N with i % q = r, f i) ^ 2) =
      ∑ z ∈ ((range N).product (range N)).filter (fun z => z.1 % q = z.2 % q), f z.1 * f z.2 := by
  let S := ((range N).product (range N)).filter (fun z => z.1 % q = z.2 % q)
  let B (r : ℕ) := (range N).filter (fun i => i % q = r)
  have hfiber (r : ℕ) : S.filter (fun z => z.1 % q = r) = (B r).product (B r) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hS, hr⟩ := mem_filter.mp hz
      obtain ⟨hT, he⟩ := mem_filter.mp hS
      obtain ⟨hi, hj⟩ := mem_product.mp hT
      exact mem_product.mpr ⟨mem_filter.mpr ⟨hi, hr⟩, mem_filter.mpr ⟨hj, he.symm.trans hr⟩⟩
    · intro hz
      obtain ⟨hx, hy⟩ := mem_product.mp hz
      obtain ⟨hi, hr⟩ := mem_filter.mp hx
      obtain ⟨hj, hs⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hi, hj⟩, hr.trans hs.symm⟩, hr⟩
  have hmap (z : ℕ × ℕ) (_ : z ∈ S) : z.1 % q ∈ range q := mem_range.mpr (Nat.mod_lt _ hq)
  refine Eq.trans ?_ (sum_fiberwise_of_maps_to hmap (fun z => f z.1 * f z.2))
  apply sum_congr rfl
  intro r _
  rw [hfiber, sq, sum_mul_sum]
  exact (sum_product (B r) (B r) (fun z => f z.1 * f z.2)).symm

open Finset

private theorem split_pairs (f : ℕ → ℝ) (N q : ℕ) :
    (∑ z ∈ ((range N).product (range N)).filter
      (fun z => z.1 % q = z.2 % q), f z.1 * f z.2) =
    (∑ i ∈ range N, f i ^ 2) + 2 * ∑ z ∈ ((range N).product (range N)).filter
      (fun z => z.1 < z.2 ∧ z.1 % q = z.2 % q), f z.1 * f z.2 := by
  let R := (range N).product (range N)
  let D := R.filter fun z => z.1 = z.2
  let U := R.filter fun z => z.1 < z.2 ∧ z.1 % q = z.2 % q
  let L := R.filter fun z => z.2 < z.1 ∧ z.1 % q = z.2 % q
  let w (z : ℕ × ℕ) := f z.1 * f z.2
  have hd : ∑ z ∈ D, w z = ∑ i ∈ range N, f i ^ 2 := by
    apply sum_nbij' Prod.fst (fun i => (i,i))
    · intro z hz
      exact (mem_product.mp (mem_filter.mp hz).1).1
    · intro i hi
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hi,hi⟩,rfl⟩
    · intro z hz
      exact Prod.ext rfl (mem_filter.mp hz).2
    · intro i hi; rfl
    · intro z hz
      simp only [w, ← (mem_filter.mp hz).2, sq]
  have hs : ∑ z ∈ L, w z = ∑ z ∈ U, w z := by
    apply sum_nbij' Prod.swap Prod.swap
    · intro z hz
      obtain ⟨h,hlt,hm⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_product.mpr (mem_product.mp h).symm, hlt, hm.symm⟩
    · intro z hz
      obtain ⟨h,hlt,hm⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_product.mpr (mem_product.mp h).symm, hlt, hm.symm⟩
    · intro z _; rfl
    · intro z _; rfl
    · intro z _; exact mul_comm _ _
  have hsum : (∑ z ∈ R.filter (fun z => z.1 % q = z.2 % q), w z) =
      (∑ z ∈ D, w z) + (∑ z ∈ U, w z) + (∑ z ∈ L, w z) := by
    simp only [D,U,L,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    rintro ⟨i,j⟩ _
    rcases lt_trichotomy i j with h|h|h
    · by_cases e : i % q = j % q <;> simp [h,h.ne,h.not_gt,e]
    · subst j; simp
    · by_cases e : i % q = j % q <;> simp [h,h.ne',h.not_gt,e]
  change _ = _ + 2 * ∑ z ∈ U, w z
  rw [← hd, two_mul]
  exact hsum.trans (by rw [hs, add_assoc])

end GoldbachResidueMass

namespace GoldbachResidueMass
open Finset

theorem shift_reindex (f : ℕ → ℝ) (N q : ℕ) (hq : 0 < q) :
    (∑ z ∈ ((range N).product (range N)).filter
      (fun z => z.1 < z.2 ∧ z.1 % q = z.2 % q), f z.1 * f z.2) =
    ∑ t ∈ Icc 1 ((N-1)/q), ∑ i ∈ range (N-q*t), f i * f (i+q*t) := by
  rw [Finset.sum_sigma']
  symm
  let toPair : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun x => (x.2, x.2 + q * x.1)
  let toShift : (ℕ × ℕ) → (Σ _ : ℕ, ℕ) := fun z => ⟨(z.2-z.1)/q, z.1⟩
  have lag (i j : ℕ) (hlt : i < j) (hmod : i % q = j % q) :
      q * ((j-i)/q) = j-i := by
    exact Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' hlt.le).mp hmod)
  apply Finset.sum_nbij' toPair toShift
  · rintro ⟨t,i⟩ hx
    simp only [mem_sigma, mem_Icc, mem_range] at hx
    have hpos : 0 < q*t := Nat.mul_pos hq (by omega)
    change (i,i+q*t) ∈ _
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, ?_, ?_⟩
    · change i < i + q*t
      omega
    · simp only [Nat.add_mul_mod_self_left]
  · rintro ⟨i,j⟩ hz
    obtain ⟨hp,hlt,hmod⟩ := mem_filter.mp hz
    have hi : i < N := mem_range.mp (mem_product.mp hp).1
    have hj : j < N := mem_range.mp (mem_product.mp hp).2
    have heq := lag i j hlt hmod
    change (⟨(j-i)/q,i⟩ : Σ _ : ℕ, ℕ) ∈ _
    simp only [mem_sigma, mem_Icc, mem_range]
    refine ⟨⟨?_, ?_⟩, by omega⟩
    · change 1 ≤ (j-i)/q
      cases hd : (j-i)/q with
      | zero =>
        rw [hd, Nat.mul_zero] at heq
        have hij : i < j := hlt
        omega
      | succ k => omega
    · apply (Nat.le_div_iff_mul_le hq).2
      rw [Nat.mul_comm, heq]
      omega
  · rintro ⟨t,i⟩ hx
    simp [toPair, toShift, Nat.mul_div_cancel_left _ hq]
  · rintro ⟨i,j⟩ hz
    obtain ⟨_,hlt,hmod⟩ := mem_filter.mp hz
    have heq := lag i j hlt hmod
    simp [toPair, toShift, heq, Nat.add_sub_of_le hlt.le]
  · rintro ⟨t,i⟩ hx
    rfl

end GoldbachResidueMass

theorem Conjectures.Cuts.Task99950cab5c8977334dbea5e5 : (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) => ∑ x4 ∈ Finset.range x3, (∑ x5 ∈ Finset.range x2 with x5 % x3 = x4, x1 x5) ^ (2 : ℕ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.Icc (1 : ℕ) ((x3 - (1 : ℕ)) / x4), ∑ x6 ∈ Finset.range (x3 - x4 * x5), x2 x6 * x2 (x6 + x4 * x5); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ), (0 : ℕ) < x5 → x1 x3 x4 x5 = ∑ x7 ∈ Finset.range x4, x3 x7 ^ (2 : ℕ) + (2 : ℝ) * x2 x3 x4 x5) := by
  intro s corr f N q hq
  dsimp only [s, corr]
  rw [GoldbachResidueMass.squared_residues f N q hq, GoldbachResidueMass.split_pairs,
    GoldbachResidueMass.shift_reindex f N q hq]
