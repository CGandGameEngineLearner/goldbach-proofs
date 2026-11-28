import Mathlib

private theorem shortProd (l : List ℕ) (h : l.length ≤ 2) (a b : ℕ)
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : l.prod = a*b := by
  match l with
  | [] => simp at ha
  | [x] => simp_all
  | [x,y] =>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with h|h <;> rcases hb with g|g <;> simp_all [Nat.mul_comm]
  | x::y::z::t => simp at h

theorem Conjectures.Cuts.Taskc2471cd7110ea42affd69679 : (∀ u v : ℕ, u ≠ v → u.primeFactorsList.length ≤ 2 → v.primeFactorsList.length ≤ 2 →
    (u.primeFactors ∩ v.primeFactors).card ≤ 1) := by
  intro u v huv hu hv
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hne
  have get (w : ℕ) (hw : w.primeFactorsList.length ≤ 2)
      (ha : a ∈ w.primeFactors) (hb : b ∈ w.primeFactors) : w=a*b := by
    have wa := Nat.mem_primeFactors.mp ha
    have wb := Nat.mem_primeFactors.mp hb
    rw [← Nat.prod_primeFactorsList wa.2.2]
    exact shortProd _ hw a b ((Nat.mem_primeFactorsList wa.2.2).mpr ⟨wa.1,wa.2.1⟩)
      ((Nat.mem_primeFactorsList wb.2.2).mpr ⟨wb.1,wb.2.1⟩) hne
  exact huv ((get u hu (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1).trans
    (get v hv (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2).symm)
