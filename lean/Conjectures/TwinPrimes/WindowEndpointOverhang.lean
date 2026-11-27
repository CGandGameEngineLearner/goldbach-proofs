import Mathlib

open scoped BigOperators

noncomputable section

namespace TwinWindow

/-- 短窗 `w X = {n : X < n < 51X/50}`（整数截断）。 -/
def w (X : ℕ) : Finset ℕ :=
  (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)

lemma w_mem {X n : ℕ} : n ∈ w X ↔ n ≤ 2*X ∧ X < n ∧ 50*n < 51*X := by
  unfold w
  rw [Finset.mem_filter, Finset.mem_range]
  omega

/-- `n ∈ w` 时 `n ≤ 2X−2`（`X ≥ 2`）。 -/
lemma w_le {X n : ℕ} (hX : 2 ≤ X) (hn : n ∈ w X) : n + 2 ≤ 2*X := by
  rw [w_mem] at hn
  obtain ⟨h2, h1, h3⟩ := hn
  -- n = 2X 或 2X−1 会与 50n < 51X 冲突
  by_contra h
  have h2X : n = 2*X ∨ n = 2*X - 1 := by omega
  rcases h2X with h | h
  · subst h; omega
  · subst h; omega

/-- 端点的“二边界”集合：`n ∈ w` 但 `n+2 ∉ w`。 -/
def T (X : ℕ) : Finset ℕ := (w X).filter (fun n => n + 2 ∉ w X)

/-- `T` 中任意两个元素相差 ≤ 1。 -/
lemma T_pair_le {X n m : ℕ} (hn : n ∈ T X) (hm : m ∈ T X) (hnm : n ≤ m) :
    m ≤ n + 1 := by
  have hw_n : n ∈ w X := (Finset.mem_filter.mp hn).1
  have hw_m : m ∈ w X := (Finset.mem_filter.mp hm).1
  have hnot_n : n + 2 ∉ w X := (Finset.mem_filter.mp hn).2
  have hnot_m : m + 2 ∉ w X := (Finset.mem_filter.mp hm).2
  rw [w_mem] at hw_n hw_m
  -- 由 hw: 50n < 51X；由 not (n+2 ∈ w): 若范围条件够，则 51X ≤ 50(n+2)
  have hXn : X < n := hw_n.2.1
  have hXm : X < m := hw_m.2.1
  have h50n : 50*n < 51*X := hw_n.2.2
  have h50m : 50*m < 51*X := hw_m.2.2
  -- n+2 ∉ w 推出 51X ≤ 50(n+2)
  have hrn : n + 2 ≤ 2*X := by
    by_contra hc
    have : n + 2 ≤ 2*X + 1 := by omega
    rw [w_mem] at hnot_n
    apply hnot_n
    have hx : X < n + 2 := by omega
    have h50 : 50*(n+2) < 51*X := by omega
    exact ⟨by omega, hx, h50⟩
  have hlow : 51*X ≤ 50*(n+2) := by
    by_contra hc
    have hle : n + 2 ≤ 2*X := hrn
    apply hnot_n
    rw [w_mem]
    exact ⟨hle, by omega, by omega⟩
  have hrm : m + 2 ≤ 2*X := by
    by_contra hc
    have hle : m + 2 ≤ 2*X + 1 := by omega
    apply hnot_m
    rw [w_mem]
    exact ⟨by omega, by omega, by omega⟩
  have hlow_m : 51*X ≤ 50*(m+2) := by
    by_contra hc
    apply hnot_m
    rw [w_mem]
    exact ⟨hrm, by omega, by omega⟩
  -- 两个不等式合并：50*(m−n) < 100
  omega

/-- `T.card ≤ 2`。 -/
lemma T_card_le_two (X : ℕ) : (T X).card ≤ 2 := by
  rcases (T X).eq_empty_or_nonempty with h | h
  · simp [h]
  · let n0 := (T X).min' h
    have hn0 : n0 ∈ T X := Finset.min'_mem (T X) h
    have hmin : ∀ n ∈ T X, n0 ≤ n := fun n hn => Finset.min'_le (T X) n hn
    have hsub : T X ⊆ {n0, n0+1} := by
      intro n hn
      have h1 : n0 ≤ n := hmin n hn
      have h2 : n ≤ n0 + 1 := T_pair_le hn0 hn h1
      have hn' : n = n0 ∨ n = n0 + 1 := by omega
      rcases hn' with h | h
      · simp [h]
      · simp [h]
    have hcard : (T X).card ≤ ({n0, n0+1} : Finset ℕ).card := Finset.card_le_card hsub
    have h2 : ({n0, n0+1} : Finset ℕ).card ≤ 2 := by
      rw [Finset.card_insert_of_notMem (by simp)]
      simp
    omega

end TwinWindow

theorem Conjectures.TwinPrimes.WindowEndpointOverhang :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); ∀ (X : ℕ) (f : ℕ → ℝ) (A : ℝ), 2 ≤ X → 0 ≤ A → (∀ n : ℕ, n ≤ 2*X+2 → 0 ≤ f n ∧ f n ≤ A) → 0 ≤ (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2)) ∧ (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2)) ≤ 2*A^2 := by
  dsimp only
  intro X f A hX hA hf
  let wX := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
  let g : ℕ → ℝ := fun n => f n * f (n+2)
  let T : Finset ℕ := wX.filter (fun n => n + 2 ∉ wX)
  have hsplit : (wX).sum g - (wX.filter (fun n => n+2 ∈ wX)).sum g = T.sum g := by
    have h := Finset.sum_filter_add_sum_filter_not (s := wX)
      (p := fun n => n + 2 ∈ wX) (f := g)
    have hT : T = wX.filter (fun n => n + 2 ∉ wX) := rfl
    rw [hT]
    linarith
  have hTcard : T.card ≤ 2 := TwinWindow.T_card_le_two X
  have hnonneg : ∀ n ∈ T, 0 ≤ g n := by
    intro n hn
    have hw : n ∈ wX := (Finset.mem_filter.mp hn).1
    rw [Finset.mem_filter, Finset.mem_range] at hw
    have hn2 : n + 2 ≤ 2*X + 2 := by omega
    have hn' : n ≤ 2*X + 2 := by omega
    have h1 := (hf n hn').1
    have h2 := (hf (n+2) hn2).1
    exact mul_nonneg h1 h2
  have hbnd : ∀ n ∈ T, g n ≤ A^2 := by
    intro n hn
    have hw : n ∈ wX := (Finset.mem_filter.mp hn).1
    rw [Finset.mem_filter, Finset.mem_range] at hw
    have hn2 : n + 2 ≤ 2*X + 2 := by omega
    have hn' : n ≤ 2*X + 2 := by omega
    have h1 := (hf n hn').2
    have h2 := (hf (n+2) hn2).2
    have h1n := (hf n hn').1
    have h2n := (hf (n+2) hn2).1
    have : f n * f (n+2) ≤ A * A := by nlinarith
    calc f n * f (n+2) ≤ A * A := this
      _ = A^2 := by ring
  have hsum_le : T.sum g ≤ T.card * A^2 := by
    calc T.sum g ≤ T.sum (fun _ => A^2) := Finset.sum_le_sum hbnd
      _ = T.card * A^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  constructor
  · rw [hsplit]
    exact Finset.sum_nonneg hnonneg
  · rw [hsplit]
    have hA2 : 0 ≤ A^2 := sq_nonneg A
    calc T.sum g ≤ T.card * A^2 := hsum_le
      _ ≤ 2 * A^2 := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hTcard) hA2
