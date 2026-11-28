import Mathlib

theorem Conjectures.Cuts.Task1559a0531ab98e6c76942c1a : (∀ (x1 x2 x3 : ℕ),   (2 : ℕ) ≤ x1 →     ∀ (x5 : Finset ℕ),       have x6 : Finset ℕ := {x6 ∈ Finset.range (x1 ^ x2) | (∀ x7 < x2, x6 / x1 ^ x7 % x1 ≤ (1 : ℕ)) ∧ {x7 ∈ Finset.range x2 | x6 / x1 ^ x7 % x1 = (1 : ℕ)}.card = x3};       have x7 : Finset (Finset ℕ) := Finset.powersetCard x3 (Finset.range x2);       have x8 : Finset ℕ → ℕ := fun (x8 : Finset ℕ) => ∑ x9 ∈ x8, x1 ^ x9;       {x9 ∈ x6 | x9 ∈ x5}.card = {x9 ∈ x7 | x8 x9 ∈ x5}.card ∧ x6.card = x2.choose x3) := by
  intro b k j hb T L P val
  have hb0 : 0 < b := by omega
  have hb1 : 1 < b := hb
  have hgeom : ∀ k, ∑ i ∈ Finset.range k, b ^ i < b ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Nat.pow_succ]
      have h2 : b ^ k + b ^ k ≤ b * b ^ k := by
        nlinarith [hb1, Nat.zero_le (b ^ k)]
      nlinarith [ih, h2, Nat.zero_le (b ^ k), Nat.zero_le (∑ i ∈ Finset.range k, b ^ i)]
  have hval_lt : ∀ s ⊆ Finset.range k, val s < b ^ k := by
    intro s hs
    exact lt_of_le_of_lt
      (Finset.sum_le_sum_of_subset (s := s) (t := Finset.range k) (f := fun i => b ^ i) hs) (hgeom k)
  have hdigit_eq : ∀ k i, i < k → ∀ x, x / b ^ i % b = x % b ^ k / b ^ i % b := by
    intro k i hi x
    have h1 : b ^ k = b ^ (k - i - 1) * b * b ^ i := by
      have h3 : b ^ k = b ^ (k - i) * b ^ i := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      rw [show k - i = (k - i - 1) + 1 by omega, Nat.pow_succ] at h3
      rw [h3]
    have hbx : x = x % b ^ k + b * (x / b ^ k * b ^ (k - i - 1)) * b ^ i := by
      calc x = b ^ k * (x / b ^ k) + x % b ^ k := (Nat.div_add_mod x (b ^ k)).symm
        _ = x % b ^ k + b * (x / b ^ k * b ^ (k - i - 1)) * b ^ i := by rw [h1]; ring
    conv_lhs => rw [hbx]
    have key : ∀ a c e : ℕ, 0 < e → (a + e * c) / e = a / e + c :=
      fun a c e he => Nat.add_mul_div_left a c he
    rw [mul_comm (b * (x / b ^ k * b ^ (k - i - 1))) (b ^ i), key _ _ _ (Nat.pow_pos hb0),
      Nat.add_mul_mod_self_left]
  have hexpand : ∀ k x, x < b ^ k → x = ∑ i ∈ Finset.range k, (x / b ^ i % b) * b ^ i := by
    intro k
    induction k with
    | zero => intro x hx; simp at hx; simp [hx]
    | succ k ih =>
      intro x hx
      have hpk : 0 < b ^ k := Nat.pow_pos hb0
      have hlt : x % b ^ k < b ^ k := Nat.mod_lt _ hpk
      have hdm : x / b ^ k % b = x / b ^ k :=
        Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hpk).2 (by rwa [← Nat.pow_succ']))
      rw [Finset.sum_range_succ]
      have hcongr : ∀ i ∈ Finset.range k, (x / b ^ i % b) * b ^ i = (x % b ^ k / b ^ i % b) * b ^ i := by
        intro i hi
        rw [hdigit_eq k i (Finset.mem_range.mp hi) x]
      rw [Finset.sum_congr rfl hcongr, ← ih (x % b ^ k) hlt, hdm]
      linarith [Nat.div_add_mod x (b ^ k)]
  have huniq : ∀ (k : ℕ) (d e : ℕ → ℕ), (∀ i < k, d i < b) → (∀ i < k, e i < b) →
      (∑ i ∈ Finset.range k, d i * b ^ i) = ∑ i ∈ Finset.range k, e i * b ^ i → ∀ i < k, d i = e i := by
    intro k
    induction k with
    | zero => intro d e _ _ _ i hi; simp at hi
    | succ k ih =>
      intro d e hd he h i hi
      have hsplit : ∀ f : ℕ → ℕ, ∑ i ∈ Finset.range (k + 1), f i * b ^ i
          = (∑ i ∈ Finset.range k, f (i + 1) * b ^ i) * b + f 0 := by
        intro f
        rw [Finset.sum_range_succ', Finset.sum_mul]
        simp only [Nat.pow_succ, Nat.pow_zero, mul_one, mul_assoc]
      rw [hsplit d, hsplit e] at h
      rw [mul_comm (∑ i ∈ Finset.range k, d (i + 1) * b ^ i) b,
          mul_comm (∑ i ∈ Finset.range k, e (i + 1) * b ^ i) b,
          Nat.add_comm (b * (∑ i ∈ Finset.range k, d (i + 1) * b ^ i)) (d 0),
          Nat.add_comm (b * (∑ i ∈ Finset.range k, e (i + 1) * b ^ i)) (e 0)] at h
      have hm : d 0 % b = e 0 % b := by
        rw [← Nat.add_mul_mod_self_left (d 0) b (∑ i ∈ Finset.range k, d (i + 1) * b ^ i),
            ← Nat.add_mul_mod_self_left (e 0) b (∑ i ∈ Finset.range k, e (i + 1) * b ^ i), h]
      rw [Nat.mod_eq_of_lt (hd 0 (by omega)), Nat.mod_eq_of_lt (he 0 (by omega))] at hm
      have hrec : ∀ i < k, d (i + 1) = e (i + 1) :=
        ih (fun i => d (i + 1)) (fun i => e (i + 1)) (fun i hi => hd (i + 1) (by omega))
          (fun i hi => he (i + 1) (by omega))
          (Nat.eq_of_mul_eq_mul_right hb0 (by linarith))
      by_cases h0 : i = 0
      · subst h0; exact hm
      · obtain ⟨i', hi'⟩ := Nat.exists_eq_succ_of_ne_zero h0
        subst hi'
        exact hrec i' (by omega)
  have hdigit : ∀ s : Finset ℕ, s ⊆ Finset.range k → ∀ i < k, val s / b ^ i % b = if i ∈ s then 1 else 0 := by
    intro s hs i hi
    have hexp := hexpand k (val s) (hval_lt s hs)
    have hsplit : val s = ∑ i' ∈ Finset.range k, (if i' ∈ s then 1 else 0) * b ^ i' := by
      dsimp only [val]
      have hfs : (Finset.range k).filter (fun i' => i' ∈ s) = s := by
        ext i'
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨-, h2⟩; exact h2
        · intro h; exact ⟨Finset.mem_range.mp (hs h), h⟩
      conv_lhs => rw [← hfs]
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun i' _ => by split <;> ring
    have hmem : ∀ i' < k, (if i' ∈ s then 1 else 0 : ℕ) < b := by
      intro i' _
      split <;> omega
    have hde := huniq k (fun i' => val s / b ^ i' % b) (fun i' => if i' ∈ s then 1 else 0)
      (fun i' _ => Nat.mod_lt _ hb0) hmem (by rw [← hexp, hsplit]) i hi
    rw [hde]
  have hDval : ∀ s ∈ P, {i ∈ Finset.range k | val s / b ^ i % b = 1} = s := by
    intro s hs
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hdigit s hsub i h1] at h2
      split at h2
      · assumption
      · exact absurd h2 (by decide)
    · intro h
      exact ⟨Finset.mem_range.mp (hsub h), by rw [hdigit s hsub i (Finset.mem_range.mp (hsub h))]; simp [h]⟩
  have hmemP : ∀ x ∈ L, {i ∈ Finset.range k | x / b ^ i % b = 1} ∈ P := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hxj⟩ := hx2
    exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hxj⟩
  have hvalL : ∀ s ∈ P, val s ∈ L := by
    intro s hs
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hval_lt s hsub),
      fun i hi => by rw [hdigit s hsub i hi]; split <;> simp,
      by rw [hDval s hs, hcard]⟩
  have hrecon : ∀ x ∈ L, x = val {i ∈ Finset.range k | x / b ^ i % b = 1} := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxd, -⟩ := hx2
    have hexp := hexpand k x (Finset.mem_range.mp hx1)
    have hsplit : ∑ i ∈ Finset.range k, (x / b ^ i % b) * b ^ i
        = val {i ∈ Finset.range k | x / b ^ i % b = 1} := by
      dsimp only [val]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hd : x / b ^ i % b ≤ 1 := hxd i (Finset.mem_range.mp hi)
      by_cases h1 : x / b ^ i % b = 1
      · rw [if_pos h1, h1, one_mul]
      · have h0 : x / b ^ i % b = 0 := by omega
        rw [if_neg h1, h0, zero_mul]
    calc x = ∑ i ∈ Finset.range k, (x / b ^ i % b) * b ^ i := hexp
      _ = val {i ∈ Finset.range k | x / b ^ i % b = 1} := hsplit
  refine ⟨?_, ?_⟩
  · refine Finset.card_nbij (fun x => {i ∈ Finset.range k | x / b ^ i % b = 1}) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxL, hxT⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hmemP x hxL, by rw [← hrecon x hxL]; exact hxT⟩
    · intro x hx y hy h
      dsimp only at h
      rw [hrecon x (Finset.mem_filter.mp hx).1, hrecon y (Finset.mem_filter.mp hy).1, h]
    · intro s hs
      obtain ⟨hsP, hsT⟩ := Finset.mem_filter.mp hs
      exact ⟨val s, Finset.mem_filter.mpr ⟨hvalL s hsP, hsT⟩, hDval s hsP⟩
  · rw [Finset.card_nbij (fun x => {i ∈ Finset.range k | x / b ^ i % b = 1}) hmemP ?_ ?_]
    · rw [Finset.card_powersetCard, Finset.card_range]
    · intro x hx y hy h
      dsimp only at h
      rw [hrecon x hx, hrecon y hy, h]
    · intro s hs
      exact ⟨val s, hvalL s hs, hDval s hs⟩
