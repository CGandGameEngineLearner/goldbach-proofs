import Mathlib

open scoped BigOperators

private def adjDigit (b n i : ℕ) := n / b ^ i % b

private def adjWords (b : ℕ) (D : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (b ^ k)).filter fun n =>
    (∀ i < k, adjDigit b n i ∈ D) ∧
      ∀ i < k - 1, adjDigit b n i ≠ adjDigit b n (i + 1)

private def adjTop (b : ℕ) (D : Finset ℕ) (k a : ℕ) :=
  (adjWords b D (k + 1)).filter (fun n => adjDigit b n k = a)

private noncomputable def adjPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I)

private theorem adjPhase_add (x y : ℕ) (t : ℝ) :
    adjPhase (x + y) t = adjPhase x t * adjPhase y t := by
  unfold adjPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem adjDigit_low {b k i : ℕ} (hb : 0 < b) (hi : i < k) (y a : ℕ) :
    adjDigit b (y + a * b ^ k) i = adjDigit b y i := by
  have hk : k = i + (k - i - 1 + 1) := by omega
  have he : b ^ k = b * b ^ (k - i - 1) * b ^ i := by
    conv_lhs => rw [hk]
    rw [pow_add, pow_succ]
    ring
  unfold adjDigit
  rw [he, ← mul_assoc, Nat.add_mul_div_right _ _ (pow_pos hb _)]
  rw [show a * (b * b ^ (k - i - 1)) = (a * b ^ (k - i - 1)) * b by ring,
    Nat.add_mul_mod_self_right]

private theorem adjDigit_high {b k y a : ℕ} (hb : 0 < b)
    (hy : y < b ^ k) (ha : a < b) :
    adjDigit b (y + a * b ^ k) k = a := by
  unfold adjDigit
  rw [Nat.add_mul_div_right _ _ (pow_pos hb _), Nat.div_eq_of_lt hy, zero_add,
    Nat.mod_eq_of_lt ha]

private def adjShift (c : ℕ) : ℕ ↪ ℕ :=
  ⟨fun y => y + c, fun _ _ h => Nat.add_right_cancel h⟩

private theorem adjTop_step {b : ℕ} {D : Finset ℕ} (hb : 0 < b)
    (hD : D ⊆ Finset.range b) (k : ℕ) {a : ℕ} (ha : a ∈ D) :
    adjTop b D (k + 1) a =
      ((adjWords b D (k + 1)).filter fun y => adjDigit b y k ≠ a).map
        (adjShift (a * b ^ (k + 1))) := by
  have hab : a < b := Finset.mem_range.mp (hD ha)
  have hp : 0 < b ^ (k + 1) := pow_pos hb _
  have hswap (y : ℕ) (hy : y < b ^ (k + 1)) :
      y + a * b ^ (k + 1) ∈ adjTop b D (k + 1) a ↔
        y ∈ (adjWords b D (k + 1)).filter (fun y => adjDigit b y k ≠ a) := by
    have low (i : ℕ) (hi : i < k + 1) := adjDigit_low hb hi y a
    have high := adjDigit_high hb hy hab
    simp only [adjTop, adjWords, Finset.mem_filter, Finset.mem_range, high, and_true]
    constructor
    · rintro ⟨_, hd, hn⟩
      refine ⟨⟨hy, ?_, ?_⟩, ?_⟩
      · exact fun i hi => (low i hi) ▸ hd i (by omega)
      · intro i hi
        simpa only [low i (by omega), low (i + 1) (by omega)] using hn i (by omega)
      · simpa only [low k (by omega), high] using hn k (by omega)
    · rintro ⟨⟨_, hd, hn⟩, he⟩
      refine ⟨?_, ?_, ?_⟩
      · calc
          y + a * b ^ (k + 1) < b ^ (k + 1) + a * b ^ (k + 1) :=
            Nat.add_lt_add_right hy _
          _ = (a + 1) * b ^ (k + 1) := by ring
          _ ≤ b * b ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
          _ = b ^ (k + 1 + 1) := (pow_succ' b (k + 1)).symm
      · intro i hi
        by_cases h : i < k + 1
        · rw [low i h]
          exact hd i h
        · have : i = k + 1 := by omega
          subst i
          rwa [high]
      · intro i hi
        by_cases h : i < k
        · rw [low i (by omega), low (i + 1) (by omega)]
          exact hn i (by omega)
        · have : i = k := by omega
          subst i
          rw [low k (by omega), high]
          exact he
  ext n
  rw [Finset.mem_map]
  constructor
  · intro hn
    have hn' := (Finset.mem_filter.mp hn)
    have hsize := Finset.mem_range.mp (Finset.mem_filter.mp hn'.1).1
    have hq : n / b ^ (k + 1) < b := by
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      simpa only [pow_succ' b (k + 1)] using hsize
    have hqa : n / b ^ (k + 1) = a := by
      simpa only [adjDigit, Nat.mod_eq_of_lt hq] using hn'.2
    let y := n % b ^ (k + 1)
    have hy : y < b ^ (k + 1) := Nat.mod_lt _ hp
    have hny : y + a * b ^ (k + 1) = n := by
      dsimp only [y]
      rw [← hqa]
      exact Nat.mod_add_div' _ _
    exact ⟨y, (hswap y hy).mp (hny.symm ▸ hn), hny⟩
  · rintro ⟨y, hy, rfl⟩
    exact (hswap y (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1)).mpr hy

private theorem adjTop_zero {b : ℕ} {D : Finset ℕ} (hD : D ⊆ Finset.range b)
    {a : ℕ} (ha : a ∈ D) : adjTop b D 0 a = {a} := by
  have hab := Finset.mem_range.mp (hD ha)
  ext n
  simp only [adjTop, adjWords, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
    zero_add, pow_one, Nat.sub_self, Nat.not_lt_zero, IsEmpty.forall_iff, and_true]
  constructor
  · rintro ⟨⟨h, _⟩, hh⟩
    simpa [adjDigit, Nat.mod_eq_of_lt h] using hh
  · rintro rfl
    refine ⟨⟨hab, ?_⟩, ?_⟩
    · refine ⟨?_, fun _ => trivial⟩
      intro i hi
      have : i = 0 := by omega
      subst i
      simpa [adjDigit, Nat.mod_eq_of_lt hab] using ha
    · simp [adjDigit, Nat.mod_eq_of_lt hab]

private theorem adjTop_fiber {b : ℕ} (D : Finset ℕ) (k a d : ℕ) (hne : d ≠ a) :
    (((adjWords b D (k + 1)).filter (fun y => adjDigit b y k ≠ a)).filter
      fun y => adjDigit b y k = d) = adjTop b D k d := by
  ext y
  simp only [adjTop, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨h, rfl⟩
    exact ⟨⟨h, hne⟩, rfl⟩

private theorem adjTop_values {b : ℕ} (hb : 0 < b) {D : Finset ℕ}
    (hD : D ⊆ Finset.range b) (k : ℕ) :
    ∀ a ∈ D,
      (∀ t : ℝ, ∑ n ∈ adjTop b D k a, adjPhase n t =
        Nat.rec (motive := fun _ => ℕ → ℝ → ℂ) adjPhase
          (fun i prev d u => adjPhase (d * b ^ (i + 1)) u *
            ∑ c ∈ D with c ≠ d, prev c u) k a t) ∧
      (adjTop b D k a).card = (D.card - 1) ^ k := by
  induction k with
  | zero =>
      intro a ha
      rw [adjTop_zero hD ha]
      simp
  | succ k ih =>
      intro a ha
      rw [adjTop_step hb hD k ha]
      let U := (adjWords b D (k + 1)).filter (fun n => adjDigit b n k ≠ a)
      let E := D.filter (fun d => d ≠ a)
      have hm : (U : Set ℕ).MapsTo (fun n => adjDigit b n k) E := by
        intro n hn
        obtain ⟨hw, hv⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).2.1 k (by omega), hv⟩
      constructor
      · intro t
        rw [Finset.sum_map]
        change (∑ y ∈ U, adjPhase (y + a * b ^ (k + 1)) t) = _
        simp_rw [adjPhase_add, ← Finset.sum_mul]
        rw [mul_comm (∑ y ∈ U, adjPhase y t)]
        congr 1
        rw [← Finset.sum_fiberwise_of_maps_to hm]
        apply Finset.sum_congr rfl
        intro d hd
        rw [adjTop_fiber D k a d (Finset.mem_filter.mp hd).2]
        exact (ih d (Finset.mem_filter.mp hd).1).1 t
      · rw [Finset.card_map]
        change U.card = (D.card - 1) ^ (k + 1)
        calc
          U.card = ∑ d ∈ E, ((U.filter fun n => adjDigit b n k = d).card) :=
            Finset.card_eq_sum_card_fiberwise hm
          _ = ∑ _d ∈ E, (D.card - 1) ^ k := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [adjTop_fiber D k a d (Finset.mem_filter.mp hd).2]
            exact (ih d (Finset.mem_filter.mp hd).1).2
          _ = _ := by
            simp only [Finset.sum_const, Nat.nsmul_eq_mul, E, Finset.filter_ne',
              Finset.card_erase_of_mem ha, pow_succ]
            ac_rfl

theorem Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * (↑x1 * x2)) * Complex.I); have x2 : ℕ → Finset ℕ → ℕ → Finset ℕ := fun (x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ) => {x5 ∈ Finset.range (x2 ^ x4) | (∀ x6 < x4, x5 / x2 ^ x6 % x2 ∈ x3) ∧ ∀ x6 < x4 - (1 : ℕ), x5 / x2 ^ x6 % x2 ≠ x5 / x2 ^ (x6 + (1 : ℕ)) % x2}; have x3 : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : Finset ℕ) (x5 : ℕ) => Nat.rec (motive := fun (x6 : ℕ) => ℕ → ℝ → ℂ) x1 (fun (x6 : ℕ) (x7 : ℕ → ℝ → ℂ) (x8 : ℕ) (x9 : ℝ) => x1 (x8 * x3 ^ (x6 + (1 : ℕ))) x9 * ∑ x10 ∈ x4 with x10 ≠ x8, x7 x10 x9) x5; ∀ (x4 : ℕ), (2 : ℕ) ≤ x4 → ∀ x6 ⊆ Finset.range x4, (2 : ℕ) ≤ x6.card → ∀ (x9 : ℕ), (∀ (x10 : ℝ), ∑ x11 ∈ x2 x4 x6 (x9 + (1 : ℕ)), x1 x11 x10 = ∑ x11 ∈ x6, x3 x4 x6 x9 x11 x10) ∧ (x2 x4 x6 (x9 + (1 : ℕ))).card = x6.card * (x6.card - (1 : ℕ)) ^ x9) := by
  classical
  dsimp only
  intro b hb D hD _ k
  have hb0 : 0 < b := by omega
  have hd : (adjWords b D (k + 1) : Set ℕ).MapsTo (fun n => adjDigit b n k) D := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2.1 k (by omega)
  change (∀ t : ℝ, ∑ n ∈ adjWords b D (k + 1), adjPhase n t =
    ∑ a ∈ D, Nat.rec (motive := fun _ => ℕ → ℝ → ℂ) adjPhase
      (fun i prev d u => adjPhase (d * b ^ (i + 1)) u *
        ∑ c ∈ D with c ≠ d, prev c u) k a t) ∧
    (adjWords b D (k + 1)).card = D.card * (D.card - 1) ^ k
  constructor
  · intro t
    rw [← Finset.sum_fiberwise_of_maps_to hd]
    exact Finset.sum_congr rfl (fun a ha => (adjTop_values hb0 hD k a ha).1 t)
  · rw [Finset.card_eq_sum_card_fiberwise hd]
    exact Finset.sum_const_nat (fun a ha => (adjTop_values hb0 hD k a ha).2)
