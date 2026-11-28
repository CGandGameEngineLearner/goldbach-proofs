import Mathlib

namespace AdjacentDigitLayers

open Finset

private def digit (b x i : ℕ) := x / b^i % b

private def words (b : ℕ) (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (range (b^k)).filter (fun x =>
    (∀ i < k, digit b x i ∈ A) ∧ ∀ i < k-1, digit b x i ≠ digit b x (i+1))

private def layer (b : ℕ) (A : Finset ℕ) (n a : ℕ) : Finset ℕ :=
  (words b A (n+1)).filter (fun x => digit b x n = a)

private theorem low (b x a k i : ℕ) (hb : 0 < b) (hi : i < k) :
    digit b (x + a*b^k) i = digit b x i := by
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show i+1 ≤ k by omega)
  have he : a*b^k = b^i * (b*(a*b^j)) := by rw [hj,pow_add,pow_succ]; ring
  simp [digit, he, Nat.add_mul_div_left, pow_pos hb]

private theorem high (b x a k : ℕ) (hb : 0 < b) (hx : x < b^k) (ha : a < b) :
    digit b (x+a*b^k) k = a := by
  simp [digit, Nat.add_mul_div_right, pow_pos hb, Nat.div_eq_of_lt hx, Nat.mod_eq_of_lt ha]

private theorem member {b x a n : ℕ} {A : Finset ℕ} (hb : 0 < b) (ha : a ∈ A)
    (hab : a < b) (hx : x < b^(n+1)) :
    x+a*b^(n+1) ∈ layer b A (n+1) a ↔ x ∈ words b A (n+1) ∧ digit b x n ≠ a := by
  have ht := high b x a (n+1) hb hx hab
  have hbound : x+a*b^(n+1) < b^(n+1+1) := by
    rw [pow_succ b (n+1)]
    have hh := Nat.mul_le_mul_left (b^(n+1)) (show a+1 ≤ b by omega)
    nlinarith only [hx,hh]
  simp only [layer,words,mem_filter,mem_range,ht,true_and,and_true,hbound,hx]
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
    · simpa only [low b x a (n+1) i hb hi] using h1 i (by omega)
    · simpa only [low b x a (n+1) i hb (by omega), low b x a (n+1) (i+1) hb (by omega)] using h2 i (by omega)
    · simpa only [low b x a (n+1) n hb (by omega),ht] using h2 n (by omega)
  · rintro ⟨⟨h1,h2⟩,hne⟩
    constructor
    · intro i hi
      by_cases h : i < n+1
      · rw [low b x a (n+1) i hb h]
        exact h1 i h
      · have : i = n+1 := by omega
        simpa [this,ht] using ha
    · intro i hi
      by_cases h : i < n
      · rw [low b x a (n+1) i hb (by omega), low b x a (n+1) (i+1) hb (by omega)]
        exact h2 i (by omega)
      · have : i = n := by omega
        simpa only [this,low b x a (n+1) n hb (by omega),ht] using hne

private theorem layer_image {b n a : ℕ} {A : Finset ℕ} (hb : 0 < b) (ha : a ∈ A) (hab : a < b) :
    layer b A (n+1) a = ((words b A (n+1)).filter (fun x => digit b x n ≠ a)).image
      (fun x => x + a*b^(n+1)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyW,ht⟩ := mem_filter.mp hy
    have hlt := mem_range.mp (mem_filter.mp hyW).1
    let q := b^(n+1)
    have hq : 0 < q := pow_pos hb _
    have hd : y/q < b := (Nat.div_lt_iff_lt_mul hq).2 (by simpa [q,pow_succ,mul_comm,mul_left_comm,mul_assoc] using hlt)
    change y/q%b = a at ht
    rw [Nat.mod_eq_of_lt hd] at ht
    have hx : y%q < q := Nat.mod_lt _ hq
    have he : y%q+a*q=y := by simpa [←ht,Nat.mul_comm] using Nat.mod_add_div y q
    apply mem_image.mpr
    refine ⟨y%q, mem_filter.mpr ((member hb ha hab hx).mp ?_), he⟩
    change y%q+a*q ∈ layer b A (n+1) a
    rwa [he]
  · intro hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨hw,hne⟩ := mem_filter.mp hx
    exact (member hb ha hab (mem_range.mp (mem_filter.mp hw).1)).mpr ⟨hw,hne⟩

private theorem base_layer {b a : ℕ} {A : Finset ℕ} (ha : a ∈ A) (hab : a < b) :
    layer b A 0 a = {a} := by
  ext x
  by_cases hx : x < b
  · simp [layer,words,digit,Nat.mod_eq_of_lt hx,hx,ha,eq_comm]
    <;> aesop
  · simp [layer,words,hx,show x ≠ a by omega]

private theorem split_sum {b : ℕ} {A : Finset ℕ} (n : ℕ) (f : ℕ → ℂ)
    (allowed : ℕ → Prop) [DecidablePred allowed] :
    ∑ x ∈ (words b A (n+1)).filter (fun x => allowed (digit b x n)), f x =
    ∑ c ∈ A.filter allowed, ∑ x ∈ layer b A n c, f x := by
  classical
  have maps : ∀ x ∈ (words b A (n+1)).filter (fun x => allowed (digit b x n)),
      digit b x n ∈ A.filter allowed := by
    intro x hx
    obtain ⟨hw,hp⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2.1 n (by omega),hp⟩
  rw [← sum_fiberwise_of_maps_to maps]
  apply sum_congr rfl
  intro c hc
  congr 1
  ext x
  have hc' := (mem_filter.mp hc).2
  simp only [mem_filter,layer]
  aesop

end AdjacentDigitLayers

open AdjacentDigitLayers Finset in
theorem Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * (↑x1 * x2)) * Complex.I); have x2 : ℕ → Finset ℕ → ℕ → Finset ℕ := fun (x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ) => {x5 ∈ Finset.range (x2 ^ x4) | (∀ x6 < x4, x5 / x2 ^ x6 % x2 ∈ x3) ∧ ∀ x6 < x4 - (1 : ℕ), x5 / x2 ^ x6 % x2 ≠ x5 / x2 ^ (x6 + (1 : ℕ)) % x2}; have x3 : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : Finset ℕ) (x5 : ℕ) => Nat.rec (motive := fun (x6 : ℕ) => ℕ → ℝ → ℂ) x1 (fun (x6 : ℕ) (x7 : ℕ → ℝ → ℂ) (x8 : ℕ) (x9 : ℝ) => x1 (x8 * x3 ^ (x6 + (1 : ℕ))) x9 * ∑ x10 ∈ x4 with x10 ≠ x8, x7 x10 x9) x5; ∀ (x4 : ℕ), (2 : ℕ) ≤ x4 → ∀ x6 ⊆ Finset.range x4, (2 : ℕ) ≤ x6.card → ∀ (x9 : ℕ), (∀ (x10 : ℝ), ∑ x11 ∈ x2 x4 x6 (x9 + (1 : ℕ)), x1 x11 x10 = ∑ x11 ∈ x6, x3 x4 x6 x9 x11 x10) ∧ (x2 x4 x6 (x9 + (1 : ℕ))).card = x6.card * (x6.card - (1 : ℕ)) ^ x9) := by
  classical
  intro E W F b hb A hA hcard n
  have hab : ∀ a ∈ A, a < b := fun a ha => mem_range.mp (hA ha)
  have hp : 0 < b := by omega
  have hadd (a x : ℕ) (t : ℝ) : E (x+a) t = E a t * E x t := by
    unfold E
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have byLayer : ∀ m a, a ∈ A → ∀ t : ℝ, (∑ x ∈ layer b A m a, E x t) = F b A m a t := by
    intro m
    induction m with
    | zero =>
      intro a ha t
      rw [base_layer ha (hab a ha),sum_singleton]
      rfl
    | succ m ih =>
      intro a ha t
      change _ = E (a*b^(m+1)) t * ∑ c ∈ A.filter (fun c => c ≠ a), F b A m c t
      rw [layer_image hp ha (hab a ha)]
      rw [sum_image (fun x _ y _ h => Nat.add_right_cancel h)]
      simp_rw [hadd]
      rw [← mul_sum, split_sum]
      congr 1
      exact sum_congr rfl fun c hc => ih c (mem_filter.mp hc).1 t
  have total (t : ℝ) : (∑ x ∈ W b A (n+1), E x t) = ∑ a ∈ A, F b A n a t := by
    change (∑ x ∈ words b A (n+1), E x t) = _
    have h := split_sum (b := b) (A := A) n (fun x => E x t) (fun _ => True)
    simpa only [Finset.filter_true_of_mem (fun _ _ => trivial)] using
      (h.trans (sum_congr (s := A.filter (fun _ => True)) rfl (fun a ha => byLayer n a (mem_filter.mp ha).1 t)))
  refine ⟨total,?_⟩
  have atZero : ∀ m a, a ∈ A → F b A m a 0 = ((A.card-1 : ℕ) : ℂ)^m := by
    intro m
    induction m with
    | zero => intro a _; simp [F,E]
    | succ m ih =>
      intro a ha
      change E (a*b^(m+1)) 0 * (∑ c ∈ A.filter (fun c => c ≠ a), F b A m c 0) = _
      have hsum := sum_congr (s := A.filter (fun c => c ≠ a)) rfl (fun c hc => ih c (mem_filter.mp hc).1)
      rw [hsum]
      have herase : A.filter (fun c => c ≠ a) = A.erase a := by ext c; simp [and_comm]
      simp [E,herase,card_erase_of_mem ha,pow_succ,mul_comm]
  have h := total 0
  have hz (x : ℕ) : E x 0 = 1 := by simp [E]
  simp_rw [hz] at h
  rw [sum_congr (s := A) rfl (fun a ha => atZero n a ha)] at h
  exact_mod_cast (show ((W b A (n+1)).card : ℂ) = ↑(A.card * (A.card-1)^n) by simpa using h)
