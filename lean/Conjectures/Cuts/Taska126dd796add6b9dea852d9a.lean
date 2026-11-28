import Mathlib

private def mass (l : List ℕ) : ℕ := (l.map (fun e => 2^e)).sum

private theorem split (l : List ℕ) (h : l.length < mass l) :
    ∃ t : List ℕ, t.length = l.length+1 ∧ mass t=mass l := by
  induction l with
  | nil => simp [mass] at h
  | cons e l ih =>
    cases e with
    | zero =>
      have hl : l.length < mass l := by
        simp [mass] at h ⊢
        omega
      obtain ⟨t,ht,hs⟩ := ih hl
      exact ⟨0::t,by simp [ht],by simpa [mass] using congrArg (fun n : ℕ => 1+n) hs⟩
    | succ e =>
      refine ⟨e::e::l,by simp,?_⟩
      simp [mass,pow_succ]; omega

private theorem extend (d : ℕ) (l : List ℕ) (h : l.length+d ≤ mass l) :
    ∃ t : List ℕ, t.length = l.length+d ∧ mass t=mass l := by
  induction d generalizing l with
  | zero => exact ⟨l,by simp,rfl⟩
  | succ d ih =>
    obtain ⟨u,hu,hm⟩ := split l (by omega)
    obtain ⟨t,ht,hs⟩ := ih u (by omega)
    exact ⟨t,by omega,hs.trans hm⟩

private theorem enumerated (l : List ℕ) : (∑ i : Fin l.length, 2^l[i.val]) = mass l := by
  induction l with
  | nil => simp [mass]
  | cons a l ih =>
    change (∑ i : Fin (l.length+1), 2^(a::l)[i.val]) = _
    rw [Fin.sum_univ_succ]
    simpa [mass] using congrArg (fun n : ℕ => 2^a+n) ih

theorem Conjectures.Cuts.Taska126dd796add6b9dea852d9a :
    ∀ m : ℕ, 13 ≤ m → m.bitIndices.length ≤ 13 →
      ∃ e : Fin 13 → ℕ, 2*m = ∑ j, 2^(e j+1) := by
  intro m hm hc
  have hs : mass m.bitIndices = m := Nat.sum_map_two_pow_bitIndices m
  obtain ⟨t,ht,hv⟩ := extend (13-m.bitIndices.length) m.bitIndices (by omega)
  have len : t.length=13 := by omega
  have arrange : ∀ n : ℕ, t.length=n → ∃ e : Fin n → ℕ, m = ∑ j, 2^(e j) := by
    rintro _ rfl
    exact ⟨fun j => t[j.val],(hv.trans hs).symm.trans (enumerated t).symm⟩
  obtain ⟨e,he⟩ := arrange 13 len
  refine ⟨e,?_⟩
  rw [he,Finset.mul_sum]
  simp [pow_succ,Nat.mul_comm]
