import Mathlib

private def quadS (p : ℕ) (a b c : ZMod p) (s : ZMod p) : ZMod p := a * s ^ 2 + b * s + c

private def sizeF (p : ℕ) [NeZero p] (a b c : ZMod p) (v : ZMod p) : ℕ :=
  (Finset.univ.filter (fun z : ZMod p × ZMod p => quadS p a b c (z.1 + z.2) = v)).card

private def discF (p : ℕ) (a b c : ZMod p) (v : ZMod p) : ZMod p := b ^ 2 - 4 * a * (c - v)

private def sqFib (p : ℕ) [NeZero p] (D : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun t : ZMod p => t ^ 2 = D)

private lemma row_card (p : ℕ) [Fact (Nat.Prime p)] (s : ZMod p) :
    (Finset.univ.filter (fun z : ZMod p × ZMod p => z.1 + z.2 = s)).card = p := by
  have hinj : Function.Injective (fun t : ZMod p => (t, s - t)) := by
    intro x y hxy
    simpa using congrArg Prod.fst hxy
  have hmem : ∀ t : ZMod p, (t, s - t) ∈
      (Finset.univ.filter (fun z : ZMod p × ZMod p => z.1 + z.2 = s)) := by
    intro t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ring
  have hset : (Finset.univ.filter (fun z : ZMod p × ZMod p => z.1 + z.2 = s))
      = Finset.univ.image (fun t : ZMod p => (t, s - t)) := by
    ext z
    constructor
    · intro hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      refine Finset.mem_image.mpr ⟨z.1, Finset.mem_univ _, ?_⟩
      ext
      · rfl
      · simp only
        linear_combination -hz
    · intro hz
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hz
      exact hmem t
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

private lemma size_eq (p : ℕ) [Fact (Nat.Prime p)] (a b c v : ZMod p) :
    sizeF p a b c v = (Finset.univ.filter (fun s : ZMod p => quadS p a b c s = v)).card * p := by
  simp only [sizeF]
  set A := Finset.univ.filter (fun s : ZMod p => quadS p a b c s = v) with hA
  have hpart : (Finset.univ.filter (fun z : ZMod p × ZMod p => quadS p a b c (z.1 + z.2) = v))
      = A.biUnion (fun s => Finset.univ.filter (fun z : ZMod p × ZMod p => z.1 + z.2 = s)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hz
      refine ⟨z.1 + z.2, ?_, rfl⟩
      simpa only [hA, Finset.mem_filter, Finset.mem_univ, true_and] using hz
    · rintro ⟨s, hs, hzs⟩
      have hs' : quadS p a b c s = v := by
        simpa only [hA, Finset.mem_filter, Finset.mem_univ, true_and] using hs
      rw [hzs]
      exact hs'
  rw [hpart, Finset.card_biUnion]
  · exact Finset.sum_const_nat (fun s _ => row_card p s)
  · intro s hs s' hs' hne
    change Disjoint (Finset.univ.filter (fun z : ZMod p × ZMod p => z.1 + z.2 = s))
      (Finset.univ.filter (fun z : ZMod p × ZMod p => z.1 + z.2 = s'))
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    exact hne (hz.symm.trans hz')

private lemma two_ne_zero_zmod (p : ℕ) [Fact (Nat.Prime p)] (h2p : 2 < p) :
    (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
  have hple : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · omega
  · omega

private lemma quad_iff_sq (p : ℕ) [Fact (Nat.Prime p)] (a b c v s : ZMod p)
    (h2 : (2 : ZMod p) ≠ 0) (ha : a ≠ 0) :
    quadS p a b c s = v ↔ (2 * a * s + b) ^ 2 = discF p a b c v := by
  have h4a : 4 * a ≠ 0 := by
    have h4 : (4 : ZMod p) = 2 * 2 := by ring
    rw [h4]
    exact mul_ne_zero (mul_ne_zero h2 h2) ha
  constructor
  · intro h
    simp only [quadS, discF] at h ⊢
    rw [← h]
    ring
  · intro h
    simp only [quadS, discF] at h ⊢
    have hfac : (4 * a) * (a * s ^ 2 + b * s + c - v) = 0 := by
      have hkey : (2 * a * s + b) ^ 2 - (b ^ 2 - 4 * a * (c - v))
          = (4 * a) * (a * s ^ 2 + b * s + c - v) := by ring
      rw [h, sub_self] at hkey
      exact hkey.symm
    have hzero : a * s ^ 2 + b * s + c - v = 0 := by
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact absurd h' h4a
      · exact h'
    exact sub_eq_zero.mp hzero

private lemma size_eq_sqFib (p : ℕ) [Fact (Nat.Prime p)] (a b c v : ZMod p)
    (h2 : (2 : ZMod p) ≠ 0) (ha : a ≠ 0) :
    (Finset.univ.filter (fun s : ZMod p => quadS p a b c s = v)).card
      = (sqFib p (discF p a b c v)).card := by
  have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
  have hinj : Function.Injective (fun s : ZMod p => 2 * a * s + b) := by
    intro x y hxy
    have h' : 2 * a * x = 2 * a * y := by linear_combination hxy
    exact mul_left_cancel₀ h2a h'
  have hstep : (Finset.univ.filter (fun s : ZMod p => quadS p a b c s = v)).card
      = ((Finset.univ.filter (fun s : ZMod p => quadS p a b c s = v)).image
          (fun s : ZMod p => 2 * a * s + b)).card :=
    (Finset.card_image_of_injective _ hinj).symm
  have himage : (Finset.univ.filter (fun s : ZMod p => quadS p a b c s = v)).image
        (fun s : ZMod p => 2 * a * s + b) = sqFib p (discF p a b c v) := by
    ext t
    constructor
    · intro ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp only [sqFib, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (quad_iff_sq p a b c v s h2 ha).mp hs
    · intro ht
      simp only [sqFib, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      refine Finset.mem_image.mpr ⟨(t - b) / (2 * a), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [quad_iff_sq p a b c v ((t - b) / (2 * a)) h2 ha]
        rw [mul_div_cancel₀ _ h2a, sub_add_cancel]
        exact ht
      · rw [mul_div_cancel₀ _ h2a, sub_add_cancel]
  rw [hstep, himage]

private lemma sq_fib_zero (p : ℕ) [Fact (Nat.Prime p)] :
    (sqFib p (0 : ZMod p)).card = 1 := by
  have hset : sqFib p (0 : ZMod p) = {0} := by
    ext t
    simp only [sqFib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact sq_eq_zero_iff
  rw [hset, Finset.card_singleton]

private lemma sq_fib_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (h2 : (2 : ZMod p) ≠ 0) (D : ZMod p)
    (hD : D ≠ 0) :
    (sqFib p D).card = 0 ∨ (sqFib p D).card = 2 := by
  by_cases hne : (sqFib p D).Nonempty
  · right
    obtain ⟨t0, ht0⟩ := hne
    simp only [sqFib, Finset.mem_filter, Finset.mem_univ, true_and] at ht0
    have ht0ne : t0 ≠ 0 := by
      intro h
      rw [h] at ht0
      exact hD (by rw [← ht0]; simp)
    have hneg : -t0 ≠ t0 := by
      intro h
      have hzero : (2 : ZMod p) * t0 = 0 := by linear_combination -h
      rcases mul_eq_zero.mp hzero with h' | h'
      · exact h2 h'
      · exact ht0ne h'
    have hset : sqFib p D = {t0, -t0} := by
      ext t
      simp only [sqFib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro ht
        have hprod : (t - t0) * (t + t0) = 0 := by
          have hsq : t ^ 2 - t0 ^ 2 = 0 := by rw [ht, ht0]; ring
          calc (t - t0) * (t + t0) = t ^ 2 - t0 ^ 2 := by ring
            _ = 0 := hsq
        rcases mul_eq_zero.mp hprod with h' | h'
        · left
          linear_combination h'
        · right
          linear_combination h'
      · rintro (rfl | rfl)
        · exact ht0
        · simp only [neg_sq]
          exact ht0
    rw [hset, Finset.card_insert_of_notMem (by simpa using hneg.symm), Finset.card_singleton]
  · left
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]

private lemma disc_eq_zero_iff (p : ℕ) [Fact (Nat.Prime p)] (a b c : ZMod p)
    (h4a : (4 : ZMod p) * a ≠ 0) (v : ZMod p) :
    discF p a b c v = 0 ↔ v = c - b ^ 2 * (4 * a)⁻¹ := by
  simp only [discF]
  constructor
  · intro h
    have h1 : b ^ 2 = 4 * a * (c - v) := by linear_combination h
    have h2 : c - v = b ^ 2 * (4 * a)⁻¹ := by
      rw [h1]
      rw [mul_comm (4 * a * (c - v)) ((4 * a)⁻¹), ← mul_assoc, inv_mul_cancel₀ h4a, one_mul]
    rw [← h2]
    ring
  · intro h
    rw [h]
    have hcc : c - (c - b ^ 2 * (4 * a)⁻¹) = b ^ 2 * (4 * a)⁻¹ := by ring
    rw [hcc]
    have hmul : 4 * a * (b ^ 2 * (4 * a)⁻¹) = b ^ 2 := by
      calc 4 * a * (b ^ 2 * (4 * a)⁻¹) = b ^ 2 * (4 * a * (4 * a)⁻¹) := by ring
        _ = b ^ 2 * 1 := by rw [mul_inv_cancel₀ h4a]
        _ = b ^ 2 := by ring
    rw [hmul, sub_self]

private lemma bucket_key (p : ℕ) [Fact (Nat.Prime p)] (a b c : ZMod p) (h2p : 2 < p)
    (ha : a ≠ 0) (v : ZMod p) :
    sizeF p a b c v = 0 ∨ sizeF p a b c v = p ∨ sizeF p a b c v = 2 * p := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p h2p
  have hk : (Finset.univ.filter (fun s : ZMod p => quadS p a b c s = v)).card
      = (sqFib p (discF p a b c v)).card := size_eq_sqFib p a b c v h2 ha
  rw [size_eq, hk]
  by_cases hD : discF p a b c v = 0
  · have hc : (sqFib p (discF p a b c v)).card = 1 := by
      rw [hD]
      exact sq_fib_zero p
    rw [hc]
    right
    left
    ring
  · rcases sq_fib_ne_zero p h2 (discF p a b c v) hD with h | h
    · left
      rw [h, zero_mul]
    · right
      right
      rw [h]

private lemma bucket_unique (p : ℕ) [Fact (Nat.Prime p)] (a b c : ZMod p) (h2p : 2 < p)
    (ha : a ≠ 0) :
    ∃! v : ZMod p, sizeF p a b c v = p := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p h2p
  have h4a : (4 : ZMod p) * a ≠ 0 := by
    have h4 : (4 : ZMod p) = 2 * 2 := by ring
    rw [h4]
    exact mul_ne_zero (mul_ne_zero h2 h2) ha
  refine ⟨c - b ^ 2 * (4 * a)⁻¹, ?_, ?_⟩
  · have hD0 : discF p a b c (c - b ^ 2 * (4 * a)⁻¹) = 0 :=
      (disc_eq_zero_iff p a b c h4a _).mpr rfl
    have hk : (Finset.univ.filter
          (fun s : ZMod p => quadS p a b c s = c - b ^ 2 * (4 * a)⁻¹)).card
        = (sqFib p (discF p a b c (c - b ^ 2 * (4 * a)⁻¹))).card :=
      size_eq_sqFib p a b c _ h2 ha
    have hc : (sqFib p (discF p a b c (c - b ^ 2 * (4 * a)⁻¹))).card = 1 := by
      rw [hD0]
      exact sq_fib_zero p
    change sizeF p a b c (c - b ^ 2 * (4 * a)⁻¹) = p
    rw [size_eq, hk, hc]
    ring
  · intro w hw
    rw [size_eq] at hw
    have hk : (Finset.univ.filter (fun s : ZMod p => quadS p a b c s = w)).card
        = (sqFib p (discF p a b c w)).card := size_eq_sqFib p a b c w h2 ha
    rw [hk] at hw
    have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).pos.ne'
    have hc1 : (sqFib p (discF p a b c w)).card = 1 := by
      by_cases hD : discF p a b c w = 0
      · rw [hD]
        exact sq_fib_zero p
      · rcases sq_fib_ne_zero p h2 (discF p a b c w) hD with h | h
        · rw [h, zero_mul] at hw
          omega
        · rw [h] at hw
          omega
    have hD0 : discF p a b c w = 0 := by
      by_contra hD
      rcases sq_fib_ne_zero p h2 (discF p a b c w) hD with h | h
      · rw [h] at hc1
        omega
      · rw [h] at hc1
        omega
    exact (disc_eq_zero_iff p a b c h4a w).mp hD0

theorem PEqualNP.Outside.L_hash_collision_lab_quadratic_bucket_spectrum :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (a b c : ZMod p), 2 < p → a ≠ 0 → let h := fun z : ZMod p × ZMod p => a*(z.1+z.2)^2+b*(z.1+z.2)+c; let size := fun v : ZMod p => (Finset.univ.filter (fun z : ZMod p × ZMod p => h z = v)).card; (∃! v, size v = p) ∧ (∀ v, size v = 0 ∨ size v = p ∨ size v = 2*p) := by
  intro p hp a b c h2p ha
  dsimp only
  change (∃! v, sizeF p a b c v = p) ∧
    (∀ v, sizeF p a b c v = 0 ∨ sizeF p a b c v = p ∨ sizeF p a b c v = 2 * p)
  exact ⟨bucket_unique p a b c h2p ha, fun v => bucket_key p a b c h2p ha v⟩
