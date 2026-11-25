import Mathlib

private lemma choose_succ_mul (a b : ℕ) (hba : b ≤ a) :
    (a + 1 - b) * Nat.choose (a + 1) b = (a + 1) * Nat.choose a b := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hba
  have h2 := Nat.choose_mul_factorial_mul_factorial (show b ≤ a + 1 by omega)
  have hsub : a + 1 - b = (a - b) + 1 := by omega
  rw [hsub] at h2 ⊢
  have hpos : 0 < b.factorial * (a - b).factorial :=
    Nat.mul_pos (Nat.factorial_pos b) (Nat.factorial_pos (a - b))
  have hfac1 : (a + 1).factorial = (a + 1) * a.factorial := Nat.factorial_succ a
  have hfac2 : (a - b + 1).factorial = (a - b + 1) * (a - b).factorial := Nat.factorial_succ (a - b)
  have hmul : ((a - b + 1) * Nat.choose (a + 1) b) * (b.factorial * (a - b).factorial) =
      ((a + 1) * Nat.choose a b) * (b.factorial * (a - b).factorial) := by
    calc ((a - b + 1) * Nat.choose (a + 1) b) * (b.factorial * (a - b).factorial)
        = Nat.choose (a + 1) b * b.factorial * ((a - b + 1) * (a - b).factorial) := by ring
      _ = Nat.choose (a + 1) b * b.factorial * (a - b + 1).factorial := by rw [← hfac2]
      _ = (a + 1).factorial := h2
      _ = (a + 1) * a.factorial := hfac1
      _ = (a + 1) * (Nat.choose a b * b.factorial * (a - b).factorial) := by rw [← h1]
      _ = ((a + 1) * Nat.choose a b) * (b.factorial * (a - b).factorial) := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

theorem PEqualNP.Outside.L_log_rank_split_area_gain :
  ∀ n r c s : ℕ, r ≤ s → s < n → c ≤ n - (s + 1) → let F := fun t => Nat.choose t r * Nat.choose (n - t) c; (F s ≤ F (s + 1) ↔ (s + 1) * c ≤ r * (n - s)) := by
  intro n r c s hrs hsn hcn
  dsimp only
  have hm : n - (s + 1) + 1 = n - s := by omega
  have hA := choose_succ_mul s r hrs
  have hB : (n - s - c) * Nat.choose (n - s) c = (n - s) * Nat.choose (n - (s + 1)) c := by
    have h := choose_succ_mul (n - (s + 1)) c hcn
    rwa [hm] at h
  have hposK : 0 < (s + 1 - r) * (n - s - c) := Nat.mul_pos (by omega) (by omega)
  have hposP : 0 < Nat.choose s r * Nat.choose (n - (s + 1)) c :=
    Nat.mul_pos (Nat.choose_pos hrs) (Nat.choose_pos hcn)
  have hL : (s + 1 - r) * (n - s - c) * (Nat.choose s r * Nat.choose (n - s) c) =
      (s + 1 - r) * (n - s) * (Nat.choose s r * Nat.choose (n - (s + 1)) c) := by
    calc (s + 1 - r) * (n - s - c) * (Nat.choose s r * Nat.choose (n - s) c)
        = (s + 1 - r) * Nat.choose s r * ((n - s - c) * Nat.choose (n - s) c) := by ring
      _ = (s + 1 - r) * Nat.choose s r * ((n - s) * Nat.choose (n - (s + 1)) c) := by rw [hB]
      _ = (s + 1 - r) * (n - s) * (Nat.choose s r * Nat.choose (n - (s + 1)) c) := by ring
  have hR : (s + 1 - r) * (n - s - c) * (Nat.choose (s + 1) r * Nat.choose (n - (s + 1)) c) =
      (s + 1) * (n - s - c) * (Nat.choose s r * Nat.choose (n - (s + 1)) c) := by
    calc (s + 1 - r) * (n - s - c) * (Nat.choose (s + 1) r * Nat.choose (n - (s + 1)) c)
        = (n - s - c) * ((s + 1 - r) * Nat.choose (s + 1) r) * Nat.choose (n - (s + 1)) c := by ring
      _ = (n - s - c) * ((s + 1) * Nat.choose s r) * Nat.choose (n - (s + 1)) c := by rw [hA]
      _ = (s + 1) * (n - s - c) * (Nat.choose s r * Nat.choose (n - (s + 1)) c) := by ring
  constructor
  · intro hle
    have hmul : (s + 1 - r) * (n - s - c) * (Nat.choose s r * Nat.choose (n - s) c) ≤
        (s + 1 - r) * (n - s - c) * (Nat.choose (s + 1) r * Nat.choose (n - (s + 1)) c) :=
      Nat.mul_le_mul_left _ hle
    rw [hL, hR] at hmul
    have hcmp : (s + 1 - r) * (n - s) ≤ (s + 1) * (n - s - c) := Nat.le_of_mul_le_mul_right hmul hposP
    have h1 : r ≤ s + 1 := by omega
    have h2 : c ≤ n - s := by omega
    zify [h1, h2] at hcmp ⊢
    nlinarith
  · intro hcr
    have h1 : r ≤ s + 1 := by omega
    have h2 : c ≤ n - s := by omega
    have hcmp : (s + 1 - r) * (n - s) ≤ (s + 1) * (n - s - c) := by
      zify [h1, h2] at hcr ⊢
      nlinarith
    have hmul : (s + 1 - r) * (n - s) * (Nat.choose s r * Nat.choose (n - (s + 1)) c) ≤
        (s + 1) * (n - s - c) * (Nat.choose s r * Nat.choose (n - (s + 1)) c) :=
      Nat.mul_le_mul_right _ hcmp
    rw [← hL, ← hR] at hmul
    exact Nat.le_of_mul_le_mul_left hmul hposK
