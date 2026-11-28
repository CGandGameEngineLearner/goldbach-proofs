import Mathlib

/-!
The highest-digit decomposition proposed in
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4545
works for any multiplicative phase on addition. The constant weight gives the count.
-/

namespace Goldbach.AdjacentDigits

open Finset

private def digit (b x i : ℕ) : ℕ := x / b ^ i % b

private def words (b : ℕ) (D : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (range (b ^ k)).filter fun x =>
    (∀ i < k, digit b x i ∈ D) ∧ ∀ i < k - 1, digit b x i ≠ digit b x (i + 1)

private def topWords (b : ℕ) (D : Finset ℕ) (k d : ℕ) : Finset ℕ :=
  (words b D (k + 1)).filter fun x => x / b ^ k = d

private theorem top_mem {b k x : ℕ} {D : Finset ℕ} (hb : 0 < b)
    (hx : x ∈ words b D (k + 1)) : x / b ^ k ∈ D := by
  obtain ⟨hx, hD, _⟩ := mem_filter.mp hx
  have hlt : x / b ^ k < b := (Nat.div_lt_iff_lt_mul (pow_pos hb k)).2 (by
    simpa only [pow_succ, mem_range, Nat.mul_comm] using hx)
  have hd := hD k (Nat.lt_succ_self k)
  simpa only [digit, Nat.mod_eq_of_lt hlt] using hd

private theorem extend_top {b k x d : ℕ} (hb : 0 < b) (hx : x < b ^ k) :
    (x + b ^ k * d) / b ^ k = d := by
  rw [Nat.add_mul_div_left x d (pow_pos hb k), Nat.div_eq_of_lt hx, zero_add]

private theorem extend_lower {b k x d i : ℕ} (hb : 0 < b) (hi : i ≤ k) :
    digit b (x + b ^ (k + 1) * d) i = digit b x i := by
  have hpow : b ^ (k + 1) * d = b ^ i * (b * (b ^ (k - i) * d)) := by
    calc
      b ^ (k + 1) * d = b ^ (i + (k - i + 1)) * d := by
        rw [show k + 1 = i + (k - i + 1) by omega]
      _ = _ := by rw [pow_add, pow_succ]; ac_rfl
  unfold digit
  rw [hpow, Nat.add_mul_div_left x _ (pow_pos hb i),
    Nat.add_mul_mod_self_left]

private theorem mem_extend {b k x d : ℕ} {D : Finset ℕ} (hb : 0 < b)
    (hx : x < b ^ (k + 1)) (hd : d ∈ D) (hdb : d < b) :
    x + b ^ (k + 1) * d ∈ topWords b D (k + 1) d ↔
      x ∈ words b D (k + 1) ∧ x / b ^ k ≠ d := by
  have htop := extend_top (d := d) hb hx
  have hlast : digit b (x + b ^ (k + 1) * d) (k + 1) = d := by
    rw [digit, htop, Nat.mod_eq_of_lt hdb]
  have hxlast : digit b x k = x / b ^ k := by
    apply Nat.mod_eq_of_lt
    exact (Nat.div_lt_iff_lt_mul (pow_pos hb k)).2 (by
      simpa only [pow_succ, Nat.mul_comm] using hx)
  have hbound : x + b ^ (k + 1) * d < b ^ (k + 1 + 1) := by
    calc
      x + b ^ (k + 1) * d < b ^ (k + 1) + b ^ (k + 1) * d :=
        Nat.add_lt_add_right hx _
      _ = b ^ (k + 1) * (d + 1) := by ring
      _ ≤ b ^ (k + 1 + 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hdb)
  simp only [topWords, words, mem_filter, mem_range]
  constructor
  · rintro ⟨⟨_, hmem, hne⟩, _⟩
    refine ⟨⟨hx, ?_, ?_⟩, ?_⟩
    · intro i hi
      simpa only [extend_lower hb (by omega : i ≤ k)] using hmem i (by omega)
    · intro i hi
      simpa only [extend_lower hb (by omega : i ≤ k),
        extend_lower hb (by omega : i + 1 ≤ k)] using hne i (by omega)
    · simpa only [extend_lower hb (le_refl k), hxlast, hlast] using hne k (by omega)
  · rintro ⟨⟨_, hmem, hne⟩, hprev⟩
    refine ⟨⟨hbound, ?_, ?_⟩, htop⟩
    · intro i hi
      by_cases hil : i ≤ k
      · rw [extend_lower hb hil]
        exact hmem i (by omega)
      · obtain rfl : i = k + 1 := by omega
        rw [hlast]
        exact hd
    · intro i hi
      by_cases hil : i < k
      · rw [extend_lower hb (by omega : i ≤ k), extend_lower hb (by omega : i + 1 ≤ k)]
        exact hne i (by omega)
      · have hik : i = k := by omega
        subst i
        rwa [extend_lower hb (le_refl k), hxlast, hlast]

private theorem topWords_zero {b d : ℕ} {D : Finset ℕ} (hd : d ∈ D) (hdb : d < b) :
    topWords b D 0 d = {d} := by
  ext x
  simp only [topWords, words, mem_filter, mem_range, zero_add, pow_zero, pow_one, Nat.div_one,
    mem_singleton, Nat.sub_self, Nat.not_lt_zero, false_implies, implies_true, and_true]
  refine ⟨fun h => h.2, ?_⟩
  rintro rfl
  refine ⟨⟨hdb, ?_⟩, rfl⟩
  intro i hi
  obtain rfl : i = 0 := by omega
  simpa [digit, Nat.mod_eq_of_lt hdb] using hd

private theorem topWords_succ {b k d : ℕ} {D : Finset ℕ} (hb : 0 < b)
    (hd : d ∈ D) (hdb : d < b) :
    topWords b D (k + 1) d =
      ((words b D (k + 1)).filter fun x => x / b ^ k ∈ D.erase d).image
        (fun x => x + b ^ (k + 1) * d) := by
  ext y
  simp only [mem_image, mem_filter, mem_erase]
  constructor
  · intro hy
    have htop := (mem_filter.mp hy).2
    let x := y % b ^ (k + 1)
    have hx : x < b ^ (k + 1) := Nat.mod_lt _ (pow_pos hb _)
    have heq : x + b ^ (k + 1) * d = y := by
      rw [← htop]
      exact Nat.mod_add_div _ _
    have h := (mem_extend hb hx hd hdb).mp (heq.symm ▸ hy)
    exact ⟨x, ⟨h.1, h.2, top_mem hb h.1⟩, heq⟩
  · rintro ⟨x, ⟨hx, hne, _⟩, rfl⟩
    exact (mem_extend hb (mem_range.mp (mem_filter.mp hx).1) hd hdb).mpr ⟨hx, hne⟩

private theorem sum_tops {R : Type*} [AddCommMonoid R] {b k : ℕ}
    {D E : Finset ℕ} (f : ℕ → R) :
    (∑ x ∈ (words b D (k + 1)).filter (fun x => x / b ^ k ∈ E), f x) =
      ∑ d ∈ E, ∑ x ∈ topWords b D k d, f x := by
  classical
  let W := (words b D (k + 1)).filter (fun x => x / b ^ k ∈ E)
  have hmap : ∀ x ∈ W, x / b ^ k ∈ E := fun _ hx => (mem_filter.mp hx).2
  rw [← sum_fiberwise_of_maps_to hmap f]
  refine sum_congr rfl fun d hd => congrArg (fun s : Finset ℕ => ∑ x ∈ s, f x) ?_
  ext x
  simp only [topWords, W, mem_filter]
  constructor
  · rintro ⟨⟨hx, _⟩, heq⟩
    exact ⟨hx, heq⟩
  · rintro ⟨hx, heq⟩
    exact ⟨⟨hx, heq.symm ▸ hd⟩, heq⟩

private def transfer {R : Type*} [CommSemiring R] (b : ℕ) (D : Finset ℕ) (f : ℕ → R)
    (k : ℕ) : ℕ → R :=
  Nat.rec f (fun k prev d => f (d * b ^ (k + 1)) * ∑ c ∈ D with c ≠ d, prev c) k

private theorem sum_topWords {R : Type*} [CommSemiring R] {b : ℕ} {D : Finset ℕ}
    (hb : 0 < b) (hD : D ⊆ range b) (f : ℕ → R) (hmul : ∀ x y, f (x + y) = f x * f y)
    (k d : ℕ) (hd : d ∈ D) :
    (∑ x ∈ topWords b D k d, f x) = transfer b D f k d := by
  induction k generalizing d with
  | zero => simp [topWords_zero hd (mem_range.mp (hD hd)), transfer]
  | succ k ih =>
      rw [topWords_succ hb hd (mem_range.mp (hD hd)), sum_image]
      · simp_rw [hmul]
        rw [← sum_mul, sum_tops, mul_comm _ (f (b ^ (k + 1) * d))]
        change _ = f (d * b ^ (k + 1)) * ∑ c ∈ D with c ≠ d, transfer b D f k c
        rw [Nat.mul_comm d (b ^ (k + 1)), filter_ne']
        congr 1
        exact sum_congr rfl fun c hc => ih c (mem_erase.mp hc).2
      · intro x _ y _ h
        exact Nat.add_right_cancel h

private theorem sum_words {R : Type*} [CommSemiring R] {b : ℕ} {D : Finset ℕ}
    (hb : 0 < b) (hD : D ⊆ range b) (f : ℕ → R) (hmul : ∀ x y, f (x + y) = f x * f y)
    (k : ℕ) :
    (∑ x ∈ words b D (k + 1), f x) = ∑ d ∈ D, transfer b D f k d := by
  have hfilter : ((words b D (k + 1)).filter (fun x => x / b ^ k ∈ D)) =
      words b D (k + 1) := filter_eq_self.mpr fun _ => top_mem hb
  rw [← hfilter, sum_tops]
  exact sum_congr rfl fun d hd => sum_topWords hb hD f hmul k d hd

private theorem transfer_one (b : ℕ) (D : Finset ℕ) (k d : ℕ) (hd : d ∈ D) :
    transfer b D (fun _ => (1 : ℕ)) k d = (D.card - 1) ^ k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
      change 1 * (∑ c ∈ D with c ≠ d, transfer b D (fun _ => (1 : ℕ)) k c) = _
      rw [one_mul, filter_ne']
      calc
        (∑ c ∈ D.erase d, transfer b D (fun _ => (1 : ℕ)) k c) =
            ∑ _c ∈ D.erase d, (D.card - 1) ^ k :=
          sum_congr rfl fun c hc => ih c (mem_erase.mp hc).2
        _ = _ := by simp [card_erase_of_mem hd, pow_succ, Nat.mul_comm]

private noncomputable def phase (x : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (↑((2 : ℝ) * Real.pi * (↑x * t)) * Complex.I)

private theorem phase_add (x y : ℕ) (t : ℝ) : phase (x + y) t = phase x t * phase y t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private noncomputable def phaseTransfer (b : ℕ) (D : Finset ℕ) (k : ℕ) : ℕ → ℝ → ℂ :=
  Nat.rec phase (fun k prev d t => phase (d * b ^ (k + 1)) t * ∑ c ∈ D with c ≠ d, prev c t) k

private theorem transfer_phase (b : ℕ) (D : Finset ℕ) (k d : ℕ) (t : ℝ) :
    transfer b D (fun x => phase x t) k d = phaseTransfer b D k d t := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
      change phase (d * b ^ (k + 1)) t * (∑ c ∈ D with c ≠ d, transfer b D
        (fun x => phase x t) k c) =
        phase (d * b ^ (k + 1)) t * ∑ c ∈ D with c ≠ d, phaseTransfer b D k c t
      congr 1
      exact sum_congr rfl fun c _ => ih c

end Goldbach.AdjacentDigits

open Goldbach.AdjacentDigits in
theorem Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * (↑x1 * x2)) * Complex.I); have x2 : ℕ → Finset ℕ → ℕ → Finset ℕ := fun (x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ) => {x5 ∈ Finset.range (x2 ^ x4) | (∀ x6 < x4, x5 / x2 ^ x6 % x2 ∈ x3) ∧ ∀ x6 < x4 - (1 : ℕ), x5 / x2 ^ x6 % x2 ≠ x5 / x2 ^ (x6 + (1 : ℕ)) % x2}; have x3 : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : Finset ℕ) (x5 : ℕ) => Nat.rec (motive := fun (x6 : ℕ) => ℕ → ℝ → ℂ) x1 (fun (x6 : ℕ) (x7 : ℕ → ℝ → ℂ) (x8 : ℕ) (x9 : ℝ) => x1 (x8 * x3 ^ (x6 + (1 : ℕ))) x9 * ∑ x10 ∈ x4 with x10 ≠ x8, x7 x10 x9) x5; ∀ (x4 : ℕ), (2 : ℕ) ≤ x4 → ∀ x6 ⊆ Finset.range x4, (2 : ℕ) ≤ x6.card → ∀ (x9 : ℕ), (∀ (x10 : ℝ), ∑ x11 ∈ x2 x4 x6 (x9 + (1 : ℕ)), x1 x11 x10 = ∑ x11 ∈ x6, x3 x4 x6 x9 x11 x10) ∧ (x2 x4 x6 (x9 + (1 : ℕ))).card = x6.card * (x6.card - (1 : ℕ)) ^ x9) := by
  change ∀ b : ℕ, 2 ≤ b → ∀ D ⊆ Finset.range b, 2 ≤ D.card → ∀ k : ℕ,
    (∀ t : ℝ, ∑ x ∈ words b D (k + 1), phase x t = ∑ d ∈ D, phaseTransfer b D k d t) ∧
      (words b D (k + 1)).card = D.card * (D.card - 1) ^ k
  intro b hb D hD _ k
  have hb' : 0 < b := by omega
  constructor
  · intro t
    rw [sum_words hb' hD (fun x => phase x t) (fun x y => phase_add x y t) k]
    exact Finset.sum_congr rfl fun d _ => transfer_phase b D k d t
  · calc
      (words b D (k + 1)).card = ∑ _x ∈ words b D (k + 1), (1 : ℕ) := by simp
      _ = ∑ d ∈ D, transfer b D (fun _ => (1 : ℕ)) k d :=
        sum_words hb' hD (fun _ => (1 : ℕ)) (fun _ _ => by simp) k
      _ = ∑ _d ∈ D, (D.card - 1) ^ k :=
        Finset.sum_congr rfl fun d hd => transfer_one b D k d hd
      _ = _ := by simp
