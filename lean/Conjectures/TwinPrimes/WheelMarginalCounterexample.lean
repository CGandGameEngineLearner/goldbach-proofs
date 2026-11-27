import Mathlib

namespace Conjectures.TwinPrimes.WheelMarginalCounterexample_aux

def ind (k m : ℕ) : ℕ → ℝ := fun n => if n = k then 1 else if n = m then 1 else 0

theorem ind_zero_or_one (k m n : ℕ) : ind k m n = 0 ∨ ind k m n = 1 := by
  unfold ind
  by_cases h1 : n = k
  · exact Or.inr (by simp [h1])
  · by_cases h2 : n = m
    · exact Or.inr (by simp [h1, h2])
    · exact Or.inl (by simp [h1, h2])

theorem ind_of_ne (k m n : ℕ) (h1 : n ≠ k) (h2 : n ≠ m) : ind k m n = 0 := by
  unfold ind
  simp [h1, h2]

theorem sum_ite_one (S : Finset ℕ) (c : ℕ) :
    S.sum (fun n => if n = c then (1 : ℝ) else 0) = if c ∈ S then 1 else 0 := by
  simpa using (Finset.sum_ite_eq' S c (fun _ : ℕ => (1 : ℝ)))

theorem sum_ind (k m : ℕ) (hkm : k ≠ m) (S : Finset ℕ) :
    S.sum (ind k m) = (if k ∈ S then (1 : ℝ) else 0) + (if m ∈ S then (1 : ℝ) else 0) := by
  have hkm2 : m ≠ k := fun h => hkm h.symm
  have key : ∀ n : ℕ, ind k m n
      = (if n = k then (1 : ℝ) else 0) + (if n = m then (1 : ℝ) else 0) := by
    intro n
    by_cases h1 : n = k
    · by_cases h2 : n = m
      · exact absurd (h1.symm.trans h2) hkm
      · simp [ind, h1, h2, hkm, hkm2]
    · by_cases h2 : n = m
      · simp [ind, h1, h2, hkm, hkm2]
      · simp [ind, h1, h2]
  calc S.sum (ind k m)
      = S.sum (fun n => (if n = k then (1 : ℝ) else 0) + (if n = m then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl (fun n _ => key n)
    _ = S.sum (fun n => if n = k then (1 : ℝ) else 0)
        + S.sum (fun n => if n = m then (1 : ℝ) else 0) := Finset.sum_add_distrib
    _ = (if k ∈ S then (1 : ℝ) else 0) + (if m ∈ S then (1 : ℝ) else 0) := by
        rw [sum_ite_one, sum_ite_one]

theorem sum_ind_gap_two (k : ℕ) (S : Finset ℕ) :
    S.sum (fun n => ind k (k + 2) n * ind k (k + 2) (n + 2))
      = if k ∈ S then (1 : ℝ) else 0 := by
  have key : ∀ n : ℕ, ind k (k + 2) n * ind k (k + 2) (n + 2)
      = if n = k then (1 : ℝ) else 0 := by
    intro n
    have a1 : k + 2 ≠ k := by omega
    have a2 : n + 2 ≠ n := by omega
    have a3 : k + 2 + 2 ≠ k := by omega
    have a4 : n + 2 + 2 ≠ n := by omega
    have a5 : k + 2 + 2 ≠ k + 2 := by omega
    have a6 : n + 2 + 2 ≠ n + 2 := by omega
    by_cases h1 : n = k
    · simp [ind, h1, a1, a2, a3, a4, a5, a6]
    · by_cases h2 : n = k + 2
      · have b1 : n ≠ k := by omega
        have b2 : n + 2 ≠ k := by omega
        have b3 : n + 2 ≠ k + 2 := by omega
        simp [ind, h2, a1, a2, a3, a4, a5, a6, b1, b2, b3]
      · simp [ind, h1, h2]
  calc S.sum (fun n => ind k (k + 2) n * ind k (k + 2) (n + 2))
      = S.sum (fun n => if n = k then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun n _ => key n)
    _ = if k ∈ S then (1 : ℝ) else 0 := sum_ite_one S k

theorem sum_ind_no_gap_two (k m : ℕ) (h1 : m ≠ k + 2) (h2 : k + 2 ≠ m)
    (h3 : m + 2 ≠ k) (h4 : m + 2 ≠ m) (S : Finset ℕ) :
    S.sum (fun n => ind k m n * ind k m (n + 2)) = 0 := by
  have key : ∀ n : ℕ, ind k m n * ind k m (n + 2) = 0 := by
    intro n
    have e1 : k + 2 ≠ k := by omega
    have e2 : n + 2 ≠ n := by omega
    by_cases hk : n = k
    · have c1 : n + 2 ≠ m := by omega
      simp [ind, hk, e1, e2, c1, h2]
    · by_cases hm : n = m
      · have c3 : n + 2 ≠ k := by omega
        simp [ind, hm, e1, e2, c3, h3, h4]
      · simp [ind, hk, hm]
  exact Finset.sum_eq_zero (fun n _ => key n)

theorem build (W : Finset ℕ) (q k : ℕ) (hq : 0 < q)
    (hkW : k ∈ W) (hk2W : k + 2 ∈ W) (hk3W : k + 2 + 2 * q ∈ W)
    (hck : Nat.Coprime k q) (hck2 : Nat.Coprime (k + 2) q)
    (hck3 : Nat.Coprime (k + 2 + 2 * q) q)
    (hmod : (k + 2) % q = (k + 2 + 2 * q) % q) :
    ∃ f g : ℕ → ℝ,
      (∀ n, (f n = 0 ∨ f n = 1) ∧ (g n = 0 ∨ g n = 1) ∧
            (¬ (n ∈ W ∧ Nat.Coprime n q) → f n = 0 ∧ g n = 0)) ∧
      (∀ b : ℕ, b < q →
        (W.filter (fun n => n % q = b)).sum f = (W.filter (fun n => n % q = b)).sum g) ∧
      W.sum (fun n => f n * f (n + 2)) = 1 ∧
      W.sum (fun n => g n * g (n + 2)) = 0 := by
  have hne1 : k ≠ k + 2 := by omega
  have hne2 : k ≠ k + 2 + 2 * q := by omega
  have hg1 : k + 2 + 2 * q ≠ k + 2 := by omega
  have hg2 : k + 2 ≠ k + 2 + 2 * q := by omega
  have hg3 : k + 2 + 2 * q + 2 ≠ k := by omega
  have hg4 : k + 2 + 2 * q + 2 ≠ k + 2 + 2 * q := by omega
  refine ⟨ind k (k + 2), ind k (k + 2 + 2 * q), ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨ind_zero_or_one k (k + 2) n, ind_zero_or_one k (k + 2 + 2 * q) n, ?_⟩
    intro hn
    have h1 : n ≠ k := by
      intro h
      apply hn
      rw [h]
      exact ⟨hkW, hck⟩
    have h2 : n ≠ k + 2 := by
      intro h
      apply hn
      rw [h]
      exact ⟨hk2W, hck2⟩
    have h3 : n ≠ k + 2 + 2 * q := by
      intro h
      apply hn
      rw [h]
      exact ⟨hk3W, hck3⟩
    exact ⟨ind_of_ne k (k + 2) n h1 h2, ind_of_ne k (k + 2 + 2 * q) n h1 h3⟩
  · intro b hb
    set S : Finset ℕ := W.filter (fun n => n % q = b) with hSdef
    have hmem2 : (k + 2) ∈ S ↔ (k + 2) % q = b := by
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr ⟨hk2W, h⟩
    have hmem3 : (k + 2 + 2 * q) ∈ S ↔ (k + 2 + 2 * q) % q = b := by
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr ⟨hk3W, h⟩
    have hiff : (k + 2) ∈ S ↔ (k + 2 + 2 * q) ∈ S := by
      rw [hmem2, hmem3, hmod]
    calc S.sum (ind k (k + 2))
        = (if k ∈ S then (1 : ℝ) else 0) + (if k + 2 ∈ S then (1 : ℝ) else 0) :=
          sum_ind k (k + 2) hne1 S
      _ = (if k ∈ S then (1 : ℝ) else 0)
          + (if k + 2 + 2 * q ∈ S then (1 : ℝ) else 0) := by
          by_cases h : (k + 2 + 2 * q) ∈ S
          · have h2 : (k + 2) ∈ S := hiff.mpr h
            simp [h, h2]
          · have h2 : ¬ ((k + 2) ∈ S) := fun hc => h (hiff.mp hc)
            simp [h, h2]
      _ = S.sum (ind k (k + 2 + 2 * q)) := (sum_ind k (k + 2 + 2 * q) hne2 S).symm
  · calc W.sum (fun n => ind k (k + 2) n * ind k (k + 2) (n + 2))
        = if k ∈ W then (1 : ℝ) else 0 := sum_ind_gap_two k W
      _ = 1 := by simp [hkW]
  · exact sum_ind_no_gap_two k (k + 2 + 2 * q) hg1 hg2 hg3 hg4 W

end Conjectures.TwinPrimes.WheelMarginalCounterexample_aux

theorem Conjectures.TwinPrimes.WheelMarginalCounterexample :
    let w := fun (X : ℕ) => (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X);
    ∀ (q X : ℕ), 0 < q → 200 * (q + 1) ≤ X →
      (∃ a : ℕ, a < q ∧ Nat.Coprime a q ∧ Nat.Coprime (a + 2) q) →
      (∃ f g : ℕ → ℝ,
        (∀ n, (f n = 0 ∨ f n = 1) ∧ (g n = 0 ∨ g n = 1) ∧
              (¬ (n ∈ w X ∧ Nat.Coprime n q) → f n = 0 ∧ g n = 0)) ∧
        (∀ a : ℕ, a < q →
          ((w X).filter (fun n => n % q = a)).sum f
            = ((w X).filter (fun n => n % q = a)).sum g) ∧
        (w X).sum (fun n => f n * f (n + 2)) = 1 ∧
        (w X).sum (fun n => g n * g (n + 2)) = 0) := by
  intro w q X hq hX ha
  obtain ⟨a, ha1, ha2, ha3⟩ := ha
  set W : Finset ℕ := (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
    with hWdef
  have hWmem : ∀ n : ℕ, n ∈ W ↔ (X < n ∧ 50 * n < 51 * X) := by
    intro n
    rw [hWdef, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨by omega, h⟩
  set k : ℕ := a + q * (X / q + 1) with hkdef
  have hdm : q * (X / q) + X % q = X := Nat.div_add_mod X q
  have hml : X % q < q := Nat.mod_lt X hq
  have hkval : k = a + q * (X / q) + q := by
    rw [hkdef, Nat.mul_succ]
    ring
  have hkgt : X < k := by omega
  have hkle : k ≤ X + 2 * q := by omega
  have hwin : 50 * (k + 2 + 2 * q) < 51 * X := by omega
  have hkW : k ∈ W := (hWmem k).mpr ⟨hkgt, by omega⟩
  have hk2W : k + 2 ∈ W := (hWmem _).mpr ⟨by omega, by omega⟩
  have hk3W : k + 2 + 2 * q ∈ W := (hWmem _).mpr ⟨by omega, hwin⟩
  have hkmod : k % q = a := by
    have h2 : k % q = a % q := by
      rw [hkdef, Nat.add_mul_mod_self_left]
    rw [h2, Nat.mod_eq_of_lt ha1]
  have hmod2 : (k + 2) % q = (a + 2) % q := by
    calc (k + 2) % q = ((k % q) + (2 % q)) % q := Nat.add_mod k 2 q
      _ = ((a % q) + (2 % q)) % q := by rw [hkmod, Nat.mod_eq_of_lt ha1]
      _ = (a + 2) % q := (Nat.add_mod a 2 q).symm
  have hca3 : Nat.Coprime ((a + 2) % q) q :=
    (ZMod.coprime_mod_iff_coprime (a + 2) q).mpr ha3
  have hcopk : Nat.Coprime k q :=
    (ZMod.coprime_mod_iff_coprime k q).mp (by rw [hkmod]; exact ha2)
  have hcopk2 : Nat.Coprime (k + 2) q :=
    (ZMod.coprime_mod_iff_coprime (k + 2) q).mp (by rw [hmod2]; exact hca3)
  have hcopk3 : Nat.Coprime (k + 2 + 2 * q) q :=
    (ZMod.coprime_mod_iff_coprime (k + 2 + 2 * q) q).mp
      (by rw [(Nat.add_mul_mod_self_right (k + 2) 2 q).trans hmod2]; exact hca3)
  have hmod : (k + 2) % q = (k + 2 + 2 * q) % q :=
    (Nat.add_mul_mod_self_right (k + 2) 2 q).symm
  exact Conjectures.TwinPrimes.WheelMarginalCounterexample_aux.build W q k hq hkW hk2W hk3W
    hcopk hcopk2 hcopk3 hmod
