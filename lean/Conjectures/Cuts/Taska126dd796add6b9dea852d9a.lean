import Mathlib.Data.Nat.BitIndices
import Mathlib.Algebra.BigOperators.Fin

private def mass (l : List ℕ) : ℕ := (l.map (fun e => 2 ^ e)).sum

private theorem splitOne (l : List ℕ) (h : l.length < mass l) :
    ∃ l' : List ℕ, l'.length = l.length + 1 ∧ mass l' = mass l := by
  induction l with
  | nil => simp [mass] at h
  | cons a l ih =>
    cases a with
    | zero =>
      simp only [mass, List.length_cons, List.map_cons, List.sum_cons, pow_zero] at h
      obtain ⟨l', hlen, hmass⟩ := ih (by unfold mass; omega)
      refine ⟨0 :: l', by simp [hlen], ?_⟩
      change 2 ^ 0 + mass l' = 2 ^ 0 + mass l
      rw [hmass]
    | succ a =>
      refine ⟨a :: a :: l, by simp, ?_⟩
      simp only [mass, List.map_cons, List.sum_cons, pow_succ]
      omega

private theorem padTo (d : ℕ) (l : List ℕ) (h : l.length + d ≤ mass l) :
    ∃ l' : List ℕ, l'.length = l.length + d ∧ mass l' = mass l := by
  induction d generalizing l with
  | zero => exact ⟨l, by simp, rfl⟩
  | succ d ih =>
    obtain ⟨k, hlen, hmass⟩ := splitOne l (by omega)
    obtain ⟨l', hlen', hmass'⟩ := ih k (by omega)
    exact ⟨l', by omega, hmass'.trans hmass⟩

theorem Conjectures.Cuts.Taska126dd796add6b9dea852d9a : (∀ (x1 : ℕ), (13 : ℕ) ≤ x1 → x1.bitIndices.length ≤ (13 : ℕ) → ∃ (x4 : Fin (13 : ℕ) → ℕ), (2 : ℕ) * x1 = ∑ x5 : Fin (13 : ℕ), (2 : ℕ) ^ (x4 x5 + (1 : ℕ))) := by
  intro m hm hbits
  have hs : mass m.bitIndices = m := Nat.sum_map_two_pow_bitIndices m
  obtain ⟨l, hl, hs'⟩ := padTo (13 - m.bitIndices.length) m.bitIndices (by omega)
  have hl13 : l.length = 13 := by omega
  have he : ∃ e : Fin 13 → ℕ, List.ofFn e = l := by
    refine ⟨fun i => l[Fin.cast hl13.symm i], ?_⟩
    apply List.ext_getElem
    · simpa using hl13.symm
    · intro i h1 h2
      simp only [List.getElem_ofFn]
      rfl
  obtain ⟨e, he⟩ := he
  have hmass : (∑ i, 2 ^ e i) = m := by
    rw [← List.sum_ofFn]
    change (List.ofFn ((fun x : ℕ => 2 ^ x) ∘ e)).sum = m
    rw [← List.map_ofFn, he]
    exact hs'.trans hs
  refine ⟨e, ?_⟩
  simp only [pow_succ]
  rw [← Finset.sum_mul, hmass, Nat.mul_comm]
