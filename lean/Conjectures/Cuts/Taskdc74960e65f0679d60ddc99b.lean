import Mathlib

theorem Conjectures.Cuts.Taskdc74960e65f0679d60ddc99b : (∀ (x1 x2 : ℕ),   x2 ≤ x1 →     have x4 : Finset ℕ := Finset.filter Nat.Prime (Finset.Icc (x1 - x2) x1);     have x5 : Finset ℕ := Finset.filter Nat.Prime (Finset.Icc x1 (x1 + x2));     ((∑ x6 ∈ x4, (Polynomial.monomial x6) (1 : ℕ)) * ∑ x6 ∈ x5, (Polynomial.monomial x6) (1 : ℕ)).coeff ((2 : ℕ) * x1) = {x6 ∈ Finset.range (x2 + (1 : ℕ)) | Nat.Prime (x1 - x6) ∧ Nat.Prime (x1 + x6)}.card) := by
  classical
  intro m h hh A B
  let pairs := (A.product B).filter (fun z => z.1 + z.2 = 2*m)
  have coeff : ((∑ p ∈ A, Polynomial.monomial p (1 : ℕ)) *
      ∑ q ∈ B, Polynomial.monomial q (1 : ℕ)).coeff (2*m) = pairs.card := by
    rw [Finset.sum_mul_sum]
    simp only [Polynomial.finsetSum_coeff, Polynomial.monomial_mul_monomial, one_mul,
      Polynomial.coeff_monomial]
    dsimp only [pairs]
    rw [← Finset.sum_boole (R := ℕ) (fun z : ℕ × ℕ => z.1 + z.2 = 2*m) (A.product B),
      Finset.sum_product]
  rw [coeff]
  apply Finset.card_bij (fun z _ => m - z.1)
  · rintro ⟨p,q⟩ hz
    obtain ⟨hpq, he⟩ := Finset.mem_filter.mp hz
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    obtain ⟨hpI,hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqI,hqP⟩ := Finset.mem_filter.mp hq
    obtain ⟨hpL,hpU⟩ := Finset.mem_Icc.mp hpI
    change p + q = 2*m at he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by dsimp; omega), by simpa only [Nat.sub_sub_self hpU] using hpP,
      by simpa only [show m + (m-p) = q by omega] using hqP⟩
  · rintro ⟨p,q⟩ hz ⟨p',q'⟩ hz' eq
    have bounds : ∀ z ∈ pairs, z.1 ≤ m ∧ z.1 + z.2 = 2*m := by
      intro z h
      obtain ⟨hu,he⟩ := Finset.mem_filter.mp h
      exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp hu).1).1).2,he⟩
    obtain ⟨h1,h2⟩ := bounds _ hz
    obtain ⟨h3,h4⟩ := bounds _ hz'
    dsimp at h1 h2 h3 h4 eq
    exact Prod.ext (by dsimp; omega) (by dsimp; omega)
  · intro d hd
    obtain ⟨hi,h1,h2⟩ := Finset.mem_filter.mp hd
    have hdle := Finset.mem_range.mp hi
    refine ⟨(m-d,m+d), ?_, by dsimp; omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, by dsimp; omega⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,h1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,h2⟩
