import Mathlib

theorem Conjectures.Cuts.Task99950cab5c8977334dbea5e5 : (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) => ∑ x4 ∈ Finset.range x3, (∑ x5 ∈ Finset.range x2 with x5 % x3 = x4, x1 x5) ^ (2 : ℕ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.Icc (1 : ℕ) ((x3 - (1 : ℕ)) / x4), ∑ x6 ∈ Finset.range (x3 - x4 * x5), x2 x6 * x2 (x6 + x4 * x5); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ), (0 : ℕ) < x5 → x1 x3 x4 x5 = ∑ x7 ∈ Finset.range x4, x3 x7 ^ (2 : ℕ) + (2 : ℝ) * x2 x3 x4 x5) := by
  classical
  dsimp only
  intro w N p hp
  let same := ((Finset.range N).product (Finset.range N)).filter
    (fun z => z.1 % p = z.2 % p)
  let diag := same.filter (fun z => z.1 = z.2)
  let upper := same.filter (fun z => z.1 < z.2)
  let lower := same.filter (fun z => z.2 < z.1)
  let term (z : ℕ × ℕ) : ℝ := w z.1 * w z.2
  have hsame (z : ℕ × ℕ) : z ∈ same ↔ z.1 < N ∧ z.2 < N ∧ z.1 % p = z.2 % p := by
    change z ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter _ ↔ _
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_assoc]
  have hup (z : ℕ × ℕ) :
      z ∈ upper ↔ (z.1 < N ∧ z.2 < N ∧ z.1 % p = z.2 % p) ∧ z.1 < z.2 := by
    simp only [upper, Finset.mem_filter, hsame]
  have hmass : (∑ a ∈ Finset.range p, (∑ i ∈ Finset.range N with i % p = a, w i)^2) =
      ∑ z ∈ same, term z := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range p) (g := fun z => z.1 % p)
      (fun z _ => Finset.mem_range.mpr (Nat.mod_lt z.1 hp)) term]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    apply congrArg (fun s : Finset (ℕ × ℕ) => ∑ z ∈ s, term z)
    ext z
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, hsame]
    constructor
    · rintro ⟨⟨h1, e1⟩, ⟨h2, e2⟩⟩
      exact ⟨⟨h1, h2, e1.trans e2.symm⟩, e1⟩
    · rintro ⟨⟨h1, h2, e⟩, e1⟩
      exact ⟨⟨h1, e1⟩, ⟨h2, e.symm.trans e1⟩⟩
  have hsplit : (∑ z ∈ same, term z) =
      (∑ z ∈ diag, term z) + (∑ z ∈ upper, term z) + ∑ z ∈ lower, term z := by
    simp only [diag, upper, lower, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rcases lt_trichotomy z.1 z.2 with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hdiag : (∑ i ∈ Finset.range N, w i ^ 2) = ∑ z ∈ diag, term z := by
    refine Finset.sum_bij' (fun i _ => (i, i)) (fun z _ => z.1) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have h := Finset.mem_range.mp hi
      exact Finset.mem_filter.mpr ⟨(hsame _).2 ⟨h, h, rfl⟩, rfl⟩
    · intro z hz
      simp only [diag, Finset.mem_filter, hsame] at hz
      exact Finset.mem_range.mpr hz.1.1
    · intro i hi
      rfl
    · intro z hz
      simp only [diag, Finset.mem_filter, hsame] at hz
      exact Prod.ext rfl hz.2
    · intro i hi
      exact pow_two (w i)
  have hswap : (∑ z ∈ lower, term z) = ∑ z ∈ upper, term z := by
    refine Finset.sum_bij' (fun z _ => z.swap) (fun z _ => z.swap) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [lower, Finset.mem_filter, hsame] at hz
      exact (hup _).2 ⟨⟨hz.1.2.1, hz.1.1, hz.1.2.2.symm⟩, hz.2⟩
    · intro z hz
      rcases (hup z).1 hz with ⟨⟨h1, h2, hmod⟩, hlt⟩
      exact Finset.mem_filter.mpr ⟨(hsame _).2 ⟨h2, h1, hmod.symm⟩, hlt⟩
    · intro z hz
      exact Prod.swap_swap z
    · intro z hz
      exact Prod.swap_swap z
    · intro z hz
      exact mul_comm _ _
  have hgap {z : ℕ × ℕ} (hz : z ∈ upper) :
      p * ((z.2 - z.1) / p) = z.2 - z.1 := by
    rcases (hup z).1 hz with ⟨⟨_, _, hmod⟩, hlt⟩
    have hd : p ∣ z.2 - z.1 := (Nat.modEq_iff_dvd' hlt.le).1 hmod
    simpa only [Nat.mod_eq_zero_of_dvd hd, zero_add] using Nat.mod_add_div (z.2 - z.1) p
  have hshift :
      (∑ k ∈ Finset.Icc 1 ((N - 1) / p), ∑ i ∈ Finset.range (N - p*k),
        w i * w (i+p*k)) = ∑ z ∈ upper, term z := by
    rw [Finset.sum_sigma' (σ := fun _ : ℕ => ℕ) (Finset.Icc 1 ((N - 1) / p))
      (fun k => Finset.range (N - p*k)) (fun k i => w i * w (i+p*k))]
    refine Finset.sum_bij' (fun ki _ => (ki.2, ki.2 + p * ki.1))
      (fun z _ => ⟨(z.2 - z.1) / p, z.1⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro ki hki
      rcases Finset.mem_sigma.mp hki with ⟨hk, hi⟩
      have hj := Finset.mem_range.mp hi
      have hkpos : 0 < ki.1 := (Finset.mem_Icc.mp hk).1
      have hpk : 0 < p * ki.1 := Nat.mul_pos hp hkpos
      exact (hup _).2 ⟨⟨by omega, by omega, (Nat.add_mul_mod_self_left _ _ _).symm⟩,
        Nat.lt_add_of_pos_right hpk⟩
    · intro z hz
      rcases (hup z).1 hz with ⟨⟨h1, h2, _⟩, hlt⟩
      have hg := hgap hz
      apply Finset.mem_sigma.mpr
      constructor
      · change (z.2 - z.1) / p ∈ Finset.Icc 1 ((N - 1) / p)
        apply Finset.mem_Icc.mpr
        constructor
        · apply Nat.succ_le_of_lt
          apply Nat.pos_of_ne_zero
          intro hz0
          rw [hz0, mul_zero] at hg
          omega
        · apply (Nat.le_div_iff_mul_le hp).2
          rw [mul_comm, hg]
          omega
      · change z.1 ∈ Finset.range (N - p * ((z.2 - z.1) / p))
        apply Finset.mem_range.mpr
        rw [hg]
        omega
    · intro ki hki
      simp only [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hp]
    · intro z hz
      have hlt := ((hup z).1 hz).2
      refine Prod.ext rfl ?_
      change z.1 + p * ((z.2 - z.1) / p) = z.2
      rw [hgap hz]
      omega
  rw [hmass, hsplit, ← hdiag, hswap, ← hshift]
  ring
