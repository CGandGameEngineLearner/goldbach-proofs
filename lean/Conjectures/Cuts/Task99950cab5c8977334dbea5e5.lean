import Mathlib

open Finset

private theorem residue_expand (a : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) :
    (∑ r ∈ range q, (∑ i ∈ (range n).filter (fun i => i % q = r), a i)^2)
    = ∑ i ∈ range n, ∑ j ∈ (range n).filter (fun j => i % q = j % q), a i * a j := by
  classical
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (i % q)]
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro j hj
    simp [eq_comm]
  · intro b hb hne
    simp [Ne.symm hne]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.mod_lt i hq))).elim

private theorem residue_split (a : ℕ → ℝ) (n q : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ (range n).filter (fun j => i % q = j % q), a i * a j)
      = (∑ i ∈ range n, (a i)^2) +
        2 * ∑ i ∈ range n, ∑ j ∈ (range n).filter (fun j => i < j ∧ i % q = j % q), a i * a j := by
  classical
  let D := ∑ i ∈ range n, ∑ j ∈ range n, if i = j then a i * a j else 0
  let U := ∑ i ∈ range n, ∑ j ∈ range n, if i < j ∧ i % q = j % q then a i * a j else 0
  let V := ∑ i ∈ range n, ∑ j ∈ range n, if j < i ∧ i % q = j % q then a i * a j else 0
  have huv : V = U := by
    dsimp [V, U]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [eq_comm, mul_comm]
  have hd : D = ∑ i ∈ range n, (a i)^2 := by
    dsimp [D]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro j hj hji
      simp [Ne.symm hji]
    · intro h
      exact (h hi).elim
  have hsplit : (∑ i ∈ range n, ∑ j ∈ (range n).filter (fun j => i % q = j % q), a i * a j) = D + U + V := by
    dsimp [D, U, V]
    simp_rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h | h | h
    · have hn : ¬ j < i := by omega
      simp [h, hn, Nat.ne_of_lt h]
    · subst j
      simp
    · have hn : ¬ i < j := by omega
      simp [h, hn, Nat.ne_of_gt h]
  rw [hsplit, huv, hd]
  dsimp [U]
  simp_rw [← Finset.sum_filter]
  ring

private theorem residue_shifts (a : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) :
    (∑ i ∈ range n, ∑ j ∈ (range n).filter (fun j => i < j ∧ i % q = j % q), a i * a j)
    = ∑ k ∈ Icc 1 ((n-1)/q), ∑ i ∈ range (n-q*k), a i * a (i+q*k) := by
  classical
  let A := ((range n) ×ˢ (range n)).filter (fun p => p.1 < p.2 ∧ p.1 % q = p.2 % q)
  let B := ((Icc 1 ((n-1)/q)) ×ˢ (range n)).filter (fun p => p.2 < n-q*p.1)
  have hA : (∑ i ∈ range n, ∑ j ∈ (range n).filter (fun j => i < j ∧ i % q = j % q), a i * a j)
      = ∑ p ∈ A, a p.1 * a p.2 := by
    dsimp [A]
    rw [Finset.sum_filter, Finset.sum_product]
    simp_rw [Finset.sum_filter]
  have hB : (∑ k ∈ Icc 1 ((n-1)/q), ∑ i ∈ range (n-q*k), a i * a (i+q*k))
      = ∑ p ∈ B, a p.2 * a (p.2+q*p.1) := by
    dsimp [B]
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro k hk
    have hs : (range n).filter (fun i => i < n-q*k) = range (n-q*k) := by
      ext i
      simp only [mem_filter, mem_range]
      omega
    rw [← Finset.sum_filter, hs]
  rw [hA, hB]
  refine Finset.sum_bij (fun p _ => ((p.2-p.1)/q,p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [A, mem_filter, mem_product, mem_range] at hp
    rcases hp with ⟨⟨hi, hj⟩, hlt, hmod⟩
    have hdvd : q ∣ p.2-p.1 := (Nat.modEq_iff_dvd' hlt.le).mp hmod
    have heq : (p.2-p.1)/q*q = p.2-p.1 := Nat.div_mul_cancel hdvd
    have hkpos : 1 ≤ (p.2-p.1)/q :=
      Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd) hq
    have hmul : (p.2-p.1)/q*q ≤ n-1 := by omega
    have hk : (p.2-p.1)/q ≤ (n-1)/q := (Nat.le_div_iff_mul_le hq).2 hmul
    simp only [B, mem_filter, mem_product, mem_Icc, mem_range]
    refine ⟨⟨⟨hkpos,hk⟩,hi⟩, ?_⟩
    have : q * ((p.2-p.1)/q) = p.2-p.1 := by simpa [Nat.mul_comm] using heq
    omega
  · intro p hp t ht heq
    simp only [A, mem_filter, mem_product, mem_range] at hp ht
    have hpd : q ∣ p.2-p.1 := (Nat.modEq_iff_dvd' hp.2.1.le).mp hp.2.2
    have htd : q ∣ t.2-t.1 := (Nat.modEq_iff_dvd' ht.2.1.le).mp ht.2.2
    have hpq := Nat.div_mul_cancel hpd
    have htq := Nat.div_mul_cancel htd
    cases p with
    | mk i j =>
      cases t with
      | mk u v =>
        simp only [Prod.mk.injEq] at heq ⊢
        simp only at hp ht hpq htq
        have hprod : (j-i)/q*q = (v-u)/q*q := congrArg (fun k => k*q) heq.1
        omega
  · intro b hb
    simp only [B, mem_filter, mem_product, mem_Icc, mem_range] at hb
    rcases hb with ⟨⟨⟨hk,hkmax⟩,hi⟩,hbound⟩
    refine ⟨(b.2,b.2+q*b.1), ?_, ?_⟩
    · simp only [A, mem_filter, mem_product, mem_range]
      refine ⟨⟨hi, ?_⟩, ?_, ?_⟩
      · omega
      · have : 0 < q*b.1 := Nat.mul_pos hq (by omega)
        omega
      · simp [Nat.add_mod]
    · cases b with
      | mk k i =>
        simp only [Prod.mk.injEq]
        simp [Nat.ne_of_gt hq]
  · intro p hp
    simp only [A, mem_filter, mem_product, mem_range] at hp
    have hdvd : q ∣ p.2-p.1 := (Nat.modEq_iff_dvd' hp.2.1.le).mp hp.2.2
    have heq := Nat.div_mul_cancel hdvd
    congr 2
    rw [Nat.mul_comm, heq]
    exact (Nat.add_sub_of_le hp.2.1.le).symm

theorem Conjectures.Cuts.Task99950cab5c8977334dbea5e5 : (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) => ∑ x4 ∈ Finset.range x3, (∑ x5 ∈ Finset.range x2 with x5 % x3 = x4, x1 x5) ^ (2 : ℕ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.Icc (1 : ℕ) ((x3 - (1 : ℕ)) / x4), ∑ x6 ∈ Finset.range (x3 - x4 * x5), x2 x6 * x2 (x6 + x4 * x5); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ), (0 : ℕ) < x5 → x1 x3 x4 x5 = ∑ x7 ∈ Finset.range x4, x3 x7 ^ (2 : ℕ) + (2 : ℝ) * x2 x3 x4 x5) := by
  intro E S a n q hq
  exact (residue_expand a n q hq).trans ((residue_split a n q).trans (by rw [residue_shifts a n q hq]))
