import Mathlib

/-!
Counting the adjacent-distinct words in base b over a digit set S, and the frequency transfer
recursion by the top digit.

A word of length m is a number below b^m whose digit at position j is x / b^j % b. Splitting off
the top digit d = x / b^m and the rest r = x % b^m gives a bijection between the words of length
m+1 with top digit d and the words of length m whose own top digit differs from d. Induction on m
then yields the count |S| * (|S| - 1)^m and the transfer of the sums of e(n t) = exp(2 pi i n t),
which is the recursion that G satisfies by its definition.
-/

namespace Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68_aux

noncomputable def chi : ℕ → ℝ → ℂ := fun (n : ℕ) (t : ℝ) =>
  Complex.exp (↑((2 : ℝ) * Real.pi * (↑n * t)) * Complex.I)

def W (b : ℕ) (S : Finset ℕ) (m : ℕ) : Finset ℕ :=
  {x ∈ Finset.range (b ^ m) | (∀ j < m, x / b ^ j % b ∈ S) ∧
    ∀ j < m - (1 : ℕ), x / b ^ j % b ≠ x / b ^ (j + (1 : ℕ)) % b}

noncomputable def G : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (b : ℕ) (S : Finset ℕ) (k : ℕ) =>
  Nat.rec (motive := fun (_ : ℕ) => ℕ → ℝ → ℂ) chi
    (fun (i : ℕ) (f : ℕ → ℝ → ℂ) (d : ℕ) (t : ℝ) =>
      chi (d * b ^ (i + (1 : ℕ))) t * ∑ c ∈ S with c ≠ d, f c t) k

def Wd (b : ℕ) (S : Finset ℕ) (m d : ℕ) : Finset ℕ :=
  (W b S (m + 1)).filter (fun x => x / b ^ m % b = d)

def Wr (b : ℕ) (S : Finset ℕ) (m d : ℕ) : Finset ℕ :=
  (W b S (m + 1)).filter (fun x => x / b ^ m % b ≠ d)

private lemma mem_W {b : ℕ} {S : Finset ℕ} {m x : ℕ} :
    x ∈ W b S m ↔ x < b ^ m ∧ ((∀ j < m, x / b ^ j % b ∈ S) ∧
      ∀ j < m - (1 : ℕ), x / b ^ j % b ≠ x / b ^ (j + (1 : ℕ)) % b) := by
  simp [W]

private lemma chi_add (a b : ℕ) (t : ℝ) : chi (a + b) t = chi a t * chi b t := by
  unfold chi
  have h : (↑((2 : ℝ) * Real.pi * (↑(a + b) * t)) : ℂ) * Complex.I =
      (↑((2 : ℝ) * Real.pi * (↑a * t)) : ℂ) * Complex.I +
        (↑((2 : ℝ) * Real.pi * (↑b * t)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add]

private lemma digit_split (b : ℕ) (hb : 0 < b) (M : ℕ) (d r j : ℕ) (hj : j < M) :
    (d * b ^ M + r) / b ^ j % b = r / b ^ j % b := by
  have hp : 0 < b ^ j := pow_pos hb j
  have h1 : d * b ^ M + r = r + b ^ j * (d * b ^ (M - j)) := by
    have hM : b ^ M = b ^ (M - j) * b ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj)]
    calc d * b ^ M + r = d * (b ^ (M - j) * b ^ j) + r := by rw [hM]
      _ = r + b ^ j * (d * b ^ (M - j)) := by ring
  rw [h1, Nat.add_mul_div_left _ _ hp]
  have h2 : M - j = (M - j - 1) + 1 := by omega
  have h3 : d * b ^ (M - j) = b * (d * b ^ (M - j - 1)) := by
    conv_lhs => rw [h2, pow_succ]
    ring
  rw [h3, Nat.add_mul_mod_self_left]

private lemma digit_top (b : ℕ) (hb : 0 < b) (M d r : ℕ) (hd : d < b) (hr : r < b ^ M) :
    (d * b ^ M + r) / b ^ M % b = d := by
  have hp : 0 < b ^ M := pow_pos hb M
  have h1 : d * b ^ M + r = r + b ^ M * d := by ring
  rw [h1, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, zero_add, Nat.mod_eq_of_lt hd]

private lemma top_mem {b : ℕ} {S : Finset ℕ} {m x : ℕ} (hx : x ∈ W b S (m + 1)) :
    x / b ^ m % b ∈ S := by
  have h := (mem_W.mp hx).2.1
  exact h m (Nat.lt_succ_self m)

private lemma Wd_empty_of_not_mem {b : ℕ} {S : Finset ℕ} (m d : ℕ) (hd : d ∉ S) :
    Wd b S m d = ∅ := by
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    have hmem := (mem_W.mp hx'.1).2.1
    have hdS : d ∈ S := by
      rw [← hx'.2]
      exact hmem m (Nat.lt_succ_self m)
    exact absurd hdS hd
  · intro h
    simp at h

private lemma Wd_succ_eq {b : ℕ} (hb : 0 < b) {S : Finset ℕ} (hS : S ⊆ Finset.range b)
    (m d : ℕ) (hd : d ∈ S) :
    Wd b S (m + 1) d = (Wr b S m d).image (fun r => d * b ^ (m + 1) + r) := by
  have hdlt : d < b := Finset.mem_range.mp (hS hd)
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨hxlt, hmem, hadj⟩ := mem_W.mp hx'.1
    have htop : x / b ^ (m + 1) % b = d := hx'.2
    have hq : x / b ^ (m + 1) < b := by
      have hxx : x < b ^ (m + 1) * b := by
        have hpw : b ^ (m + 1 + 1) = b ^ (m + 1) * b := by ring
        rw [hpw] at hxlt
        exact hxlt
      exact Nat.div_lt_of_lt_mul hxx
    have hqd : x / b ^ (m + 1) = d := by
      rw [← htop, Nat.mod_eq_of_lt hq]
    have hrlt : x % b ^ (m + 1) < b ^ (m + 1) := Nat.mod_lt _ (pow_pos hb _)
    have hxr : d * b ^ (m + 1) + x % b ^ (m + 1) = x := by
      have h := Nat.div_add_mod x (b ^ (m + 1))
      rw [hqd, mul_comm] at h
      exact h
    refine Finset.mem_image.mpr ⟨x % b ^ (m + 1), Finset.mem_filter.mpr ⟨?_, ?_⟩, hxr⟩
    · refine mem_W.mpr ⟨hrlt, ?_, ?_⟩
      · intro j hj
        rw [← digit_split b hb (m + 1) d (x % b ^ (m + 1)) j hj, hxr]
        exact hmem j (by omega)
      · intro j hj
        rw [← digit_split b hb (m + 1) d (x % b ^ (m + 1)) j (by omega),
          ← digit_split b hb (m + 1) d (x % b ^ (m + 1)) (j + 1) (by omega), hxr]
        exact hadj j (by omega)
    · rw [← digit_split b hb (m + 1) d (x % b ^ (m + 1)) m (by omega), hxr]
      intro hcon
      exact (hadj m (by omega)) (hcon.trans htop.symm)
  · intro hx
    obtain ⟨r, hr, hxr⟩ := Finset.mem_image.mp hx
    have hr' := Finset.mem_filter.mp hr
    obtain ⟨hrlt, hmem, hadj⟩ := mem_W.mp hr'.1
    have hne : r / b ^ m % b ≠ d := hr'.2
    refine Finset.mem_filter.mpr ⟨mem_W.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [← hxr]
      have h1 : d * b ^ (m + 1) + r < (d + 1) * b ^ (m + 1) := by
        calc d * b ^ (m + 1) + r < d * b ^ (m + 1) + b ^ (m + 1) :=
              Nat.add_lt_add_left hrlt _
          _ = (d + 1) * b ^ (m + 1) := by ring
      have h2 : (d + 1) * b ^ (m + 1) ≤ b * b ^ (m + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : b * b ^ (m + 1) = b ^ (m + 1 + 1) := by ring
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (le_of_eq h3)
    · intro j hj
      rw [← hxr]
      by_cases hj' : j < m + 1
      · rw [digit_split b hb (m + 1) d r j hj']
        exact hmem j hj'
      · have hje : j = m + 1 := by omega
        rw [hje, digit_top b hb (m + 1) d r hdlt hrlt]
        exact hd
    · intro j hj
      rw [← hxr]
      by_cases hj' : j < m
      · rw [digit_split b hb (m + 1) d r j (by omega),
          digit_split b hb (m + 1) d r (j + 1) (by omega)]
        exact hadj j (by omega)
      · have hje : j = m := by omega
        rw [hje, digit_split b hb (m + 1) d r m (by omega),
          digit_top b hb (m + 1) d r hdlt hrlt]
        exact hne
    · rw [← hxr, digit_top b hb (m + 1) d r hdlt hrlt]

private lemma sum_Wr_of {b : ℕ} {S : Finset ℕ} {m : ℕ}
    (h : ∀ c t, ∑ x ∈ Wd b S m c, chi x t = if c ∈ S then G b S m c t else 0)
    (d : ℕ) (t : ℝ) :
    ∑ x ∈ Wr b S m d, chi x t = ∑ c ∈ S with c ≠ d, G b S m c t := by
  have hpt : ∀ x ∈ W b S (m + 1),
      (∑ c ∈ S with c ≠ d, if x / b ^ m % b = c then chi x t else 0) =
        if x / b ^ m % b ≠ d then chi x t else 0 := by
    intro x hx
    rw [Finset.sum_ite_eq]
    have ht : x / b ^ m % b ∈ S := top_mem hx
    simp [Finset.mem_filter, ht]
  rw [Wr, Finset.sum_filter, Finset.sum_congr rfl fun x hx => (hpt x hx).symm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc' : c ∈ S := (Finset.mem_filter.mp hc).1
  have hh := h c t
  simp only [Wd] at hh
  rw [← Finset.sum_filter, hh]
  simp [hc']

private lemma card_Wr_of {b : ℕ} {S : Finset ℕ} {m : ℕ}
    (h : ∀ c, (Wd b S m c).card = if c ∈ S then (S.card - 1) ^ m else 0) (d : ℕ) :
    (Wr b S m d).card = ∑ _c ∈ S with _c ≠ d, (S.card - 1) ^ m := by
  have hpt : ∀ x ∈ W b S (m + 1),
      (∑ c ∈ S with c ≠ d, if x / b ^ m % b = c then (1 : ℕ) else 0) =
        if x / b ^ m % b ≠ d then 1 else 0 := by
    intro x hx
    rw [Finset.sum_ite_eq]
    have ht : x / b ^ m % b ∈ S := top_mem hx
    simp [Finset.mem_filter, ht]
  calc (Wr b S m d).card
      = ∑ x ∈ W b S (m + 1), if x / b ^ m % b ≠ d then 1 else 0 := by
        rw [Wr, Finset.card_filter]
    _ = ∑ x ∈ W b S (m + 1), ∑ c ∈ S with c ≠ d, if x / b ^ m % b = c then 1 else 0 :=
        Finset.sum_congr rfl fun x hx => (hpt x hx).symm
    _ = ∑ c ∈ S with c ≠ d, ∑ x ∈ W b S (m + 1), if x / b ^ m % b = c then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ c ∈ S with c ≠ d, (Wd b S m c).card := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hh := Finset.card_filter (fun x => x / b ^ m % b = c) (W b S (m + 1))
        simp only [Wd]
        exact hh.symm
    _ = ∑ _c ∈ S with _c ≠ d, (S.card - 1) ^ m := by
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [h c]
        have hc' : c ∈ S := (Finset.mem_filter.mp hc).1
        simp [hc']

private lemma ind_sum_card {b : ℕ} (hb : 0 < b) {S : Finset ℕ} (hS : S ⊆ Finset.range b)
    (m : ℕ) :
    (∀ d t, ∑ x ∈ Wd b S m d, chi x t = if d ∈ S then G b S m d t else 0) ∧
    (∀ d, (Wd b S m d).card = if d ∈ S then (S.card - 1) ^ m else 0) := by
  induction m with
  | zero =>
    have hW : W b S 1 = S := by
      ext x
      rw [mem_W]
      have h11 : (1 : ℕ) - 1 = 0 := rfl
      rw [h11, pow_one]
      constructor
      · rintro ⟨hxb, hmem, _⟩
        have h0 : x / b ^ 0 % b = x := by
          rw [pow_zero, Nat.div_one, Nat.mod_eq_of_lt hxb]
        rw [← h0]
        exact hmem 0 (by omega)
      · intro hxS
        have hxb : x < b := Finset.mem_range.mp (hS hxS)
        refine ⟨hxb, ?_, ?_⟩
        · intro j hj
          have hj0 : j = 0 := by omega
          subst hj0
          rw [pow_zero, Nat.div_one, Nat.mod_eq_of_lt hxb]
          exact hxS
        · intro j hj
          omega
    have hWd : ∀ d, Wd b S 0 d = S.filter (fun x => x = d) := by
      intro d
      ext x
      simp only [Wd, hW, Finset.mem_filter, pow_zero, Nat.div_one]
      constructor
      · rintro ⟨hxS, hxd⟩
        exact ⟨hxS, by rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp (hS hxS))] at hxd⟩
      · rintro ⟨hxS, hxd⟩
        exact ⟨hxS, by rw [Nat.mod_eq_of_lt (Finset.mem_range.mp (hS hxS)), hxd]⟩
    constructor
    · intro d t
      rw [hWd d, Finset.sum_filter, Finset.sum_ite_eq']
      rfl
    · intro d
      rw [hWd d, Finset.card_filter, Finset.sum_ite_eq', pow_zero]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro d t
      by_cases hd : d ∈ S
      · have hinj : Set.InjOn (fun r : ℕ => d * b ^ (m + 1) + r) ↑(Wr b S m d) := by
          intro a _ b _ hab
          exact Nat.add_left_cancel hab
        rw [Wd_succ_eq hb hS m d hd, Finset.sum_image hinj]
        have hchi : ∀ r, chi (d * b ^ (m + 1) + r) t = chi (d * b ^ (m + 1)) t * chi r t :=
          fun r => chi_add _ _ _
        simp_rw [hchi]
        rw [← Finset.mul_sum, sum_Wr_of ih1 d t, ite_eq_left hd]
        rfl
      · rw [Wd_empty_of_not_mem (m + 1) d hd]
        simp [hd]
    · intro d
      by_cases hd : d ∈ S
      · have hinj : Function.Injective (fun r : ℕ => d * b ^ (m + 1) + r) := by
          intro a b hab
          exact Nat.add_left_cancel hab
        rw [Wd_succ_eq hb hS m d hd, Finset.card_image_of_injective _ hinj,
          card_Wr_of ih2 d, Finset.sum_const, nsmul_eq_mul]
        simp only [Nat.cast_id]
        have hcard : (S.filter (fun c => c ≠ d)).card = S.card - 1 := by
          have hfe : S.filter (fun c => c ≠ d) = S.erase d := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
            constructor
            · rintro ⟨hc, hne⟩; exact ⟨hne, hc⟩
            · rintro ⟨hne, hc⟩; exact ⟨hc, hne⟩
          rw [hfe, Finset.card_erase_of_mem hd]
        rw [hcard, ite_eq_left hd, ← pow_succ']
      · rw [Wd_empty_of_not_mem (m + 1) d hd]
        simp [hd]

private lemma final {b : ℕ} (hb : 0 < b) {S : Finset ℕ} (hS : S ⊆ Finset.range b) (m : ℕ) :
    (∀ t : ℝ, ∑ x ∈ W b S (m + 1), chi x t = ∑ d ∈ S, G b S m d t) ∧
    (W b S (m + 1)).card = S.card * (S.card - 1) ^ m := by
  obtain ⟨h1, h2⟩ := ind_sum_card hb hS m
  constructor
  · intro t
    have hpt : ∀ x ∈ W b S (m + 1),
        (∑ d ∈ S, if x / b ^ m % b = d then chi x t else 0) = chi x t := by
      intro x hx
      rw [Finset.sum_ite_eq]
      have ht : x / b ^ m % b ∈ S := top_mem hx
      simp [ht]
    rw [← Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hh := h1 d t
    simp only [Wd] at hh
    rw [← Finset.sum_filter, hh]
    simp [hd]
  · have hpt : ∀ x ∈ W b S (m + 1),
        (∑ d ∈ S, if x / b ^ m % b = d then (1 : ℕ) else 0) = 1 := by
      intro x hx
      rw [Finset.sum_ite_eq]
      have ht : x / b ^ m % b ∈ S := top_mem hx
      simp [ht]
    rw [Finset.card_eq_sum_ones, ← Finset.sum_congr rfl hpt, Finset.sum_comm]
    have : (∑ d ∈ S, ∑ x ∈ W b S (m + 1), if x / b ^ m % b = d then (1 : ℕ) else 0) =
        ∑ d ∈ S, (Wd b S m d).card := by
      refine Finset.sum_congr rfl fun d _ => ?_
      have hh := Finset.card_filter (fun x => x / b ^ m % b = d) (W b S (m + 1))
      simp only [Wd]
      exact hh.symm
    rw [this]
    have : (∑ d ∈ S, (Wd b S m d).card) = ∑ _d ∈ S, (S.card - 1) ^ m := by
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [h2 d]
      simp [hd]
    rw [this]
    have hsc : (∑ _d ∈ S, (S.card - 1) ^ m) = S.card * (S.card - 1) ^ m := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [hsc]

end Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68_aux

theorem Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68 :
    have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * (↑x1 * x2)) * Complex.I); have x2 : ℕ → Finset ℕ → ℕ → Finset ℕ := fun (x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ) => {x5 ∈ Finset.range (x2 ^ x4) | (∀ x6 < x4, x5 / x2 ^ x6 % x2 ∈ x3) ∧ ∀ x6 < x4 - (1 : ℕ), x5 / x2 ^ x6 % x2 ≠ x5 / x2 ^ (x6 + (1 : ℕ)) % x2}; have x3 : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : Finset ℕ) (x5 : ℕ) => Nat.rec (motive := fun (x6 : ℕ) => ℕ → ℝ → ℂ) x1 (fun (x6 : ℕ) (x7 : ℕ → ℝ → ℂ) (x8 : ℕ) (x9 : ℝ) => x1 (x8 * x3 ^ (x6 + (1 : ℕ))) x9 * ∑ x10 ∈ x4 with x10 ≠ x8, x7 x10 x9) x5; ∀ (x4 : ℕ), (2 : ℕ) ≤ x4 → ∀ x6 ⊆ Finset.range x4, (2 : ℕ) ≤ x6.card → ∀ (x9 : ℕ), (∀ (x10 : ℝ), ∑ x11 ∈ x2 x4 x6 (x9 + (1 : ℕ)), x1 x11 x10 = ∑ x11 ∈ x6, x3 x4 x6 x9 x11 x10) ∧ (x2 x4 x6 (x9 + (1 : ℕ))).card = x6.card * (x6.card - (1 : ℕ)) ^ x9 := by
  intro x1 x2 x3 x4 hx4 x6 hx6 _ x9
  exact Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68_aux.final (by omega) hx6 x9
