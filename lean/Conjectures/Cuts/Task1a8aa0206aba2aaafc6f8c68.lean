import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AdjacentDigitWords

def digit (b x i : ℕ) : ℕ := x / b ^ i % b

noncomputable def words (b : ℕ) (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (b ^ k)).filter fun x =>
    (∀ i < k, digit b x i ∈ A) ∧
      ∀ i < k - 1, digit b x i ≠ digit b x (i + 1)

noncomputable def fiber (b : ℕ) (A : Finset ℕ) (k a : ℕ) : Finset ℕ :=
  (words b A (k + 1)).filter fun x => digit b x k = a

theorem mem_words {b x k : ℕ} {A : Finset ℕ} :
    x ∈ words b A k ↔
      x < b ^ k ∧ (∀ i < k, digit b x i ∈ A) ∧
        ∀ i < k - 1, digit b x i ≠ digit b x (i + 1) := by
  simp only [words, Finset.mem_filter, Finset.mem_range]

theorem mem_fiber {b x k a : ℕ} {A : Finset ℕ} :
    x ∈ fiber b A k a ↔ x ∈ words b A (k + 1) ∧ digit b x k = a := by
  simp only [fiber, Finset.mem_filter]

theorem div_add_multiple (d x y : ℕ) (hd : 0 < d) :
    (x + y * d) / d = x / d + y := by
  have h : (x + y * d) / d = x / d + y ∧
      (x + y * d) % d = x % d := by
    apply (Nat.div_mod_unique hd).2
    constructor
    · calc
        x % d + d * (x / d + y) =
            (x % d + d * (x / d)) + y * d := by ring
        _ = x + y * d := by rw [Nat.mod_add_div]
    · exact Nat.mod_lt x hd
  exact h.1

theorem digit_shift_low (b r a n i : ℕ) (hb : 0 < b) (hi : i < n) :
    digit b (r + a * b ^ n) i = digit b r i := by
  have hp : b ^ n = b ^ i * (b * b ^ (n - (i + 1))) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hm : a * (b ^ i * (b * b ^ (n - (i + 1)))) =
      (a * b ^ (n - (i + 1)) * b) * b ^ i := by ring
  unfold digit
  rw [hp, hm, div_add_multiple _ _ _ (pow_pos hb _)]
  simp [Nat.add_mod]

theorem digit_shift_top (b r a n : ℕ) (hb : 0 < b)
    (hr : r < b ^ n) (ha : a < b) :
    digit b (r + a * b ^ n) n = a := by
  unfold digit
  rw [div_add_multiple _ _ _ (pow_pos hb _), Nat.div_eq_of_lt hr]
  simp [Nat.mod_eq_of_lt ha]

theorem top_mem {b k x : ℕ} {A : Finset ℕ}
    (hx : x ∈ words b A (k + 1)) : digit b x k ∈ A :=
  (mem_words.mp hx).2.1 k (by omega)

theorem append_mem_fiber (b : ℕ) (hb : 2 ≤ b) (A : Finset ℕ)
    (hA : A ⊆ Finset.range b) (k a r : ℕ) (ha : a ∈ A)
    (hr : r ∈ words b A (k + 1)) (hne : digit b r k ≠ a) :
    r + a * b ^ (k + 1) ∈ fiber b A (k + 1) a := by
  have hb0 : 0 < b := by omega
  have ha0 : a < b := Finset.mem_range.mp (hA ha)
  have hw := mem_words.mp hr
  have ht := digit_shift_top b r a (k + 1) hb0 hw.1 ha0
  apply mem_fiber.mpr
  refine ⟨mem_words.mpr ⟨?_, ?_, ?_⟩, ht⟩
  · calc
      r + a * b ^ (k + 1) < b ^ (k + 1) + a * b ^ (k + 1) :=
        Nat.add_lt_add_right hw.1 _
      _ = (a + 1) * b ^ (k + 1) := by ring
      _ ≤ b * b ^ (k + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = b ^ ((k + 1) + 1) := (pow_succ' b (k + 1)).symm
  · intro i hi
    by_cases hil : i < k + 1
    · rw [digit_shift_low b r a (k + 1) i hb0 hil]
      exact hw.2.1 i hil
    · have he : i = k + 1 := by omega
      subst i
      rw [ht]
      exact ha
  · intro i hi
    by_cases hik : i < k
    · rw [digit_shift_low b r a (k + 1) i hb0 (by omega),
          digit_shift_low b r a (k + 1) (i + 1) hb0 (by omega)]
      exact hw.2.2 i (by omega)
    · have he : i = k := by omega
      subst i
      rw [digit_shift_low b r a (k + 1) k hb0 (by omega), ht]
      exact hne

theorem remove_top (b : ℕ) (hb : 2 ≤ b) (A : Finset ℕ)
    (k a x : ℕ) (hx : x ∈ fiber b A (k + 1) a) :
    x % b ^ (k + 1) ∈ words b A (k + 1) ∧
      digit b (x % b ^ (k + 1)) k ≠ a ∧
        x = x % b ^ (k + 1) + a * b ^ (k + 1) := by
  have hb0 : 0 < b := by omega
  have hbpow : 0 < b ^ (k + 1) := pow_pos hb0 _
  obtain ⟨hxw, hxt⟩ := mem_fiber.mp hx
  have hw := mem_words.mp hxw
  have hq : x / b ^ (k + 1) < b := by
    apply (Nat.div_lt_iff_lt_mul hbpow).2
    simpa only [pow_succ'] using hw.1
  have hqa : x / b ^ (k + 1) = a := by
    simpa only [digit, Nat.mod_eq_of_lt hq] using hxt
  have he : x = x % b ^ (k + 1) + a * b ^ (k + 1) := by
    have h := Nat.mod_add_div x (b ^ (k + 1))
    rw [hqa] at h
    simpa only [Nat.mul_comm] using h.symm
  have hlo (i : ℕ) (hi : i < k + 1) :
      digit b (x % b ^ (k + 1)) i = digit b x i := by
    calc
      digit b (x % b ^ (k + 1)) i =
          digit b (x % b ^ (k + 1) + a * b ^ (k + 1)) i :=
        (digit_shift_low b (x % b ^ (k + 1)) a (k + 1) i hb0 hi).symm
      _ = digit b x i := congrArg (fun z => digit b z i) he.symm
  refine ⟨mem_words.mpr ⟨Nat.mod_lt _ hbpow, ?_, ?_⟩, ?_, he⟩
  · intro i hi
    rw [hlo i hi]
    exact hw.2.1 i (by omega)
  · intro i hi
    rw [hlo i (by omega), hlo (i + 1) (by omega)]
    exact hw.2.2 i (by omega)
  · intro hbad
    apply hw.2.2 k (by omega)
    calc
      digit b x k = digit b (x % b ^ (k + 1)) k := (hlo k (by omega)).symm
      _ = a := hbad
      _ = digit b x (k + 1) := hxt.symm

theorem fiber_zero (b : ℕ) (hb : 2 ≤ b) (A : Finset ℕ)
    (hA : A ⊆ Finset.range b) (a : ℕ) (ha : a ∈ A) :
    fiber b A 0 a = {a} := by
  have ha0 : a < b := Finset.mem_range.mp (hA ha)
  ext x
  constructor
  · intro hx
    obtain ⟨hxw, hxt⟩ := mem_fiber.mp hx
    have hxb : x < b := by simpa only [zero_add, pow_one] using (mem_words.mp hxw).1
    have hxa : x = a := by
      simpa only [digit, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hxb] using hxt
    exact Finset.mem_singleton.mpr hxa
  · intro hx
    have hxa := Finset.mem_singleton.mp hx
    subst x
    apply mem_fiber.mpr
    constructor
    · apply mem_words.mpr
      refine ⟨by simpa using ha0, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simpa only [digit, pow_zero, Nat.div_one, Nat.mod_eq_of_lt ha0] using ha
      · intro i hi
        omega
    · simp only [digit, pow_zero, Nat.div_one, Nat.mod_eq_of_lt ha0]

theorem sum_fiber_step (b : ℕ) (hb : 2 ≤ b) (A : Finset ℕ)
    (hA : A ⊆ Finset.range b) (k a : ℕ) (ha : a ∈ A) (f : ℕ → ℂ) :
    (∑ x ∈ fiber b A (k + 1) a, f x) =
      ∑ r ∈ (words b A (k + 1)).filter (fun r => digit b r k ≠ a),
        f (r + a * b ^ (k + 1)) := by
  symm
  refine Finset.sum_bij (fun r _ => r + a * b ^ (k + 1)) ?_ ?_ ?_ ?_
  · intro r hr
    exact append_mem_fiber b hb A hA k a r ha
      (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2
  · intro r hr z hz he
    exact Nat.add_right_cancel he
  · intro x hx
    obtain ⟨hl, hn, he⟩ := remove_top b hb A k a x hx
    exact ⟨x % b ^ (k + 1), Finset.mem_filter.mpr ⟨hl, hn⟩, he.symm⟩
  · intro r hr
    rfl

theorem sum_fibers (b : ℕ) (A : Finset ℕ) (k : ℕ) (f : ℕ → ℂ) :
    (∑ a ∈ A, ∑ x ∈ fiber b A k a, f x) =
      ∑ x ∈ words b A (k + 1), f x := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun x hx => top_mem hx) f

theorem sum_filtered_fibers (b : ℕ) (A : Finset ℕ)
    (k a : ℕ) (f : ℕ → ℂ) :
    (∑ c ∈ A with c ≠ a, ∑ x ∈ fiber b A k c, f x) =
      ∑ x ∈ (words b A (k + 1)).filter (fun x => digit b x k ≠ a), f x := by
  unfold fiber
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · apply Finset.filter_congr
    intro x hx
    simp only [Finset.mem_filter, top_mem hx, true_and]
  · intro x hx
    rfl

noncomputable def phase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((2 : ℝ) * Real.pi * ((n : ℝ) * t) : ℝ) * Complex.I)

theorem phase_add (m n : ℕ) (t : ℝ) :
    phase (m + n) t = phase m t * phase n t := by
  simp only [phase, Nat.cast_add, add_mul, mul_add, Complex.ofReal_add, Complex.exp_add]

theorem phase_at_zero (n : ℕ) : phase n 0 = 1 := by
  simp [phase]

noncomputable def transfer (b : ℕ) (A : Finset ℕ) (n : ℕ) : ℕ → ℝ → ℂ :=
  Nat.rec (motive := fun _ : ℕ => ℕ → ℝ → ℂ) phase
    (fun k f a t => phase (a * b ^ (k + 1)) t * ∑ c ∈ A with c ≠ a, f c t) n

theorem transfer_zero (b : ℕ) (A : Finset ℕ) (a : ℕ) (t : ℝ) :
    transfer b A 0 a t = phase a t := rfl

theorem transfer_succ (b : ℕ) (A : Finset ℕ) (k a : ℕ) (t : ℝ) :
    transfer b A (k + 1) a t =
      phase (a * b ^ (k + 1)) t * ∑ c ∈ A with c ≠ a, transfer b A k c t := rfl

theorem fiber_fourier (b : ℕ) (hb : 2 ≤ b) (A : Finset ℕ)
    (hA : A ⊆ Finset.range b) (k a : ℕ) (ha : a ∈ A) (t : ℝ) :
    (∑ x ∈ fiber b A k a, phase x t) = transfer b A k a t := by
  induction k generalizing a with
  | zero =>
      rw [fiber_zero b hb A hA a ha, Finset.sum_singleton, transfer_zero]
  | succ k ih =>
      calc
        (∑ x ∈ fiber b A (k + 1) a, phase x t) =
            ∑ r ∈ (words b A (k + 1)).filter (fun r => digit b r k ≠ a),
              phase (r + a * b ^ (k + 1)) t :=
          sum_fiber_step b hb A hA k a ha _
        _ = phase (a * b ^ (k + 1)) t *
            ∑ r ∈ (words b A (k + 1)).filter (fun r => digit b r k ≠ a), phase r t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [phase_add, mul_comm]
        _ = phase (a * b ^ (k + 1)) t *
            ∑ c ∈ A with c ≠ a, ∑ r ∈ fiber b A k c, phase r t := by
          rw [sum_filtered_fibers]
        _ = phase (a * b ^ (k + 1)) t *
            ∑ c ∈ A with c ≠ a, transfer b A k c t := by
          congr 1
          apply Finset.sum_congr rfl
          intro c hc
          exact ih c (Finset.mem_filter.mp hc).1
        _ = transfer b A (k + 1) a t := (transfer_succ b A k a t).symm

theorem total_fourier (b : ℕ) (hb : 2 ≤ b) (A : Finset ℕ)
    (hA : A ⊆ Finset.range b) (k : ℕ) (t : ℝ) :
    (∑ x ∈ words b A (k + 1), phase x t) = ∑ a ∈ A, transfer b A k a t := by
  calc
    _ = ∑ a ∈ A, ∑ x ∈ fiber b A k a, phase x t := (sum_fibers b A k _).symm
    _ = _ := Finset.sum_congr rfl (fun a ha => fiber_fourier b hb A hA k a ha t)

theorem transfer_at_zero (b : ℕ) (A : Finset ℕ) (k a : ℕ) (ha : a ∈ A) :
    transfer b A k a 0 = (((A.card - 1) ^ k : ℕ) : ℂ) := by
  induction k generalizing a with
  | zero => simp [transfer_zero, phase_at_zero]
  | succ k ih =>
      rw [transfer_succ, phase_at_zero, one_mul]
      calc
        (∑ c ∈ A with c ≠ a, transfer b A k c 0) =
            ∑ c ∈ A with c ≠ a, (((A.card - 1) ^ k : ℕ) : ℂ) :=
          Finset.sum_congr rfl (fun c hc => ih c (Finset.mem_filter.mp hc).1)
        _ = ((A.card - 1 : ℕ) : ℂ) * (((A.card - 1) ^ k : ℕ) : ℂ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.filter_ne',
            Finset.card_erase_of_mem ha]
        _ = (((A.card - 1) ^ (k + 1) : ℕ) : ℂ) := by
          rw [pow_succ, Nat.cast_mul]
          ring

theorem total_card (b : ℕ) (hb : 2 ≤ b) (A : Finset ℕ)
    (hA : A ⊆ Finset.range b) (k : ℕ) :
    (words b A (k + 1)).card = A.card * (A.card - 1) ^ k := by
  have hc : ((words b A (k + 1)).card : ℂ) =
      ((A.card * (A.card - 1) ^ k : ℕ) : ℂ) := by
    calc
      ((words b A (k + 1)).card : ℂ) =
          ∑ x ∈ words b A (k + 1), phase x 0 := by
        simp only [phase_at_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ a ∈ A, transfer b A k a 0 := total_fourier b hb A hA k 0
      _ = ∑ a ∈ A, (((A.card - 1) ^ k : ℕ) : ℂ) :=
        Finset.sum_congr rfl (fun a ha => transfer_at_zero b A k a ha)
      _ = ((A.card * (A.card - 1) ^ k : ℕ) : ℂ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
  exact Nat.cast_injective hc

end AdjacentDigitWords

theorem Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68 : have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * (↑x1 * x2)) * Complex.I); have x2 : ℕ → Finset ℕ → ℕ → Finset ℕ := fun (x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ) => {x5 ∈ Finset.range (x2 ^ x4) | (∀ x6 < x4, x5 / x2 ^ x6 % x2 ∈ x3) ∧ ∀ x6 < x4 - (1 : ℕ), x5 / x2 ^ x6 % x2 ≠ x5 / x2 ^ (x6 + (1 : ℕ)) % x2}; have x3 : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : Finset ℕ) (x5 : ℕ) => Nat.rec (motive := fun (x6 : ℕ) => ℕ → ℝ → ℂ) x1 (fun (x6 : ℕ) (x7 : ℕ → ℝ → ℂ) (x8 : ℕ) (x9 : ℝ) => x1 (x8 * x3 ^ (x6 + (1 : ℕ))) x9 * ∑ x10 ∈ x4 with x10 ≠ x8, x7 x10 x9) x5; ∀ (x4 : ℕ), (2 : ℕ) ≤ x4 → ∀ x6 ⊆ Finset.range x4, (2 : ℕ) ≤ x6.card → ∀ (x9 : ℕ), (∀ (x10 : ℝ), ∑ x11 ∈ x2 x4 x6 (x9 + (1 : ℕ)), x1 x11 x10 = ∑ x11 ∈ x6, x3 x4 x6 x9 x11 x10) ∧ (x2 x4 x6 (x9 + (1 : ℕ))).card = x6.card * (x6.card - (1 : ℕ)) ^ x9 := by
  change ∀ b : ℕ, 2 ≤ b → ∀ A ⊆ Finset.range b, 2 ≤ A.card → ∀ k : ℕ,
    (∀ t : ℝ, (∑ x ∈ AdjacentDigitWords.words b A (k + 1),
      AdjacentDigitWords.phase x t) = ∑ a ∈ A, AdjacentDigitWords.transfer b A k a t) ∧
      (AdjacentDigitWords.words b A (k + 1)).card = A.card * (A.card - 1) ^ k
  intro b hb A hA hcard k
  exact ⟨AdjacentDigitWords.total_fourier b hb A hA k,
    AdjacentDigitWords.total_card b hb A hA k⟩
