import Mathlib

/-- The smaller factor of a product of two primes is its minimal prime factor. -/
private theorem minPair {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≤ b) :
    (a * b).minFac = a := by
  have hp : ((a * b).minFac).Prime :=
    Nat.minFac_prime (by have := ha.two_le; have := hb.two_le; nlinarith)
  have hle := Nat.minFac_le_of_dvd ha.two_le (show a ∣ a * b from dvd_mul_right _ _)
  rcases hp.dvd_mul.mp (Nat.minFac_dvd (a * b)) with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hp ha).mp h
  · have := (Nat.prime_dvd_prime_iff_eq hp hb).mp h
    omega

/-- Reindex the sum over shifted Chen window primes by the canonical ordered factor pair;
this adapts the reindexing argument posted for this frozen task in GitHub Discussions 4711. -/
theorem Conjectures.Cuts.Task22a1f2e8c464aa2148d56f42 :
    ∀ (x1 : ℕ) (x2 : ℕ → Polynomial ℕ),
      have x3 : Finset ℕ :=
        {x3 ∈ Finset.range (x1 + (1 : ℕ)) |
          Nat.Prime x3 ∧
            have x4 : ℕ := (x3 + (2 : ℕ)).minFac;
            have x5 : ℕ := (x3 + (2 : ℕ)) / x4;
            Nat.Prime x5 ∧ x4 ^ (4 : ℕ) ≤ x5 ∧ x5 ≤ x4 ^ (5 : ℕ)}
      have x4 : Finset (ℕ × ℕ) :=
        {x4 ∈ (Finset.range (x1 + (3 : ℕ))).product (Finset.range (x1 + (3 : ℕ))) |
          Nat.Prime x4.1 ∧ Nat.Prime x4.2 ∧ x4.1 ^ (4 : ℕ) ≤ x4.2 ∧ x4.2 ≤ x4.1 ^ (5 : ℕ) ∧
            x4.1 * x4.2 ≤ x1 + (2 : ℕ) ∧ Nat.Prime (x4.1 * x4.2 - (2 : ℕ))}
      ∑ x5 ∈ x3, x2 (x5 + (2 : ℕ)) = ∑ x5 ∈ x4, x2 (x5.1 * x5.2) := by
  classical
  intro N w S F
  let enc := fun p : ℕ => ((p + 2).minFac, (p + 2) / (p + 2).minFac)
  let dec := fun z : ℕ × ℕ => z.1 * z.2 - 2
  have encprod (p : ℕ) : (enc p).1 * (enc p).2 = p + 2 :=
    Nat.mul_div_cancel' (Nat.minFac_dvd _)
  have decode (p : ℕ) : dec (enc p) = p := by
    dsimp only [dec]
    rw [encprod]
    omega
  have encode (z : ℕ × ℕ) (hz : z ∈ F) : enc (dec z) = z := by
    rcases z with ⟨a, b⟩
    obtain ⟨_, ha, hb, hl, hu, hN, hp⟩ := Finset.mem_filter.mp hz
    have hab : a ≤ b := (Nat.le_self_pow (by decide : 4 ≠ 0) _).trans hl
    have hh : 2 ≤ a * b := by have := ha.two_le; have := hb.two_le; nlinarith
    simp only [enc, dec, Nat.sub_add_cancel hh, minPair ha hb hab, Nat.mul_div_cancel_left _ ha.pos]
  apply Finset.sum_bij' (fun p _ => enc p) (fun z _ => dec z)
  · intro p hp
    obtain ⟨hn, hprime, hb, hl, hu⟩ := Finset.mem_filter.mp hp
    have hn' := Finset.mem_range.mp hn
    have prod := encprod p
    have ha : (enc p).1.Prime := Nat.minFac_prime (by omega)
    have bpos := hb.pos
    change Nat.Prime (enc p).2 at hb
    have bd1 := Nat.le_of_dvd (show 0 < p + 2 by omega) (show (enc p).1 ∣ p + 2 from ⟨_, prod.symm⟩)
    have bd2 := Nat.le_of_dvd (show 0 < p + 2 by omega) (show (enc p).2 ∣ p + 2 from ⟨(enc p).1, by rw [Nat.mul_comm]; exact prod.symm⟩)
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ha, hb, hl, hu, by omega, ?_⟩
    change Nat.Prime (dec (enc p))
    simpa only [decode] using hprime
  · intro z hz
    obtain ⟨_, ha, hb, hl, hu, hN, hp⟩ := Finset.mem_filter.mp hz
    have hzrec := encode z hz
    have ea := congrArg Prod.fst hzrec
    have eb := congrArg Prod.snd hzrec
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [dec]; omega), hp, ?_⟩
    change (enc (dec z)).2.Prime ∧ (enc (dec z)).1 ^ 4 ≤ (enc (dec z)).2 ∧ (enc (dec z)).2 ≤ (enc (dec z)).1 ^ 5
    simpa only [hzrec] using And.intro hb (And.intro hl hu)
  · exact fun p _ => decode p
  · exact encode
  · intro p hp
    exact congrArg w (encprod p).symm
