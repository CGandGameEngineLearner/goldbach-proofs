import Mathlib

/-! Expand the squared residue masses and group the off-diagonal pairs by their positive difference. -/

namespace LagSquare
open Finset

theorem expand (w : ℕ → ℝ) (X d : ℕ) (hd : 0 < d) :
    (∑ c ∈ range d, (∑ u ∈ (range X).filter (fun u => u % d = c), w u)^2) =
      ∑ u ∈ range X, ∑ v ∈ range X, if u % d = v % d then w u*w v else 0 := by
  let S c := ∑ v ∈ (range X).filter (fun v => v % d = c), w v
  have hmaps (u : ℕ) (_ : u ∈ range X) : u % d ∈ range d :=
    mem_range.mpr (Nat.mod_lt u hd)
  calc
    _ = ∑ c ∈ range d, ∑ u ∈ (range X).filter (fun u => u % d = c), w u*S (u % d) := by
      apply sum_congr rfl
      intro c _
      rw [pow_two,sum_mul]
      apply sum_congr rfl
      intro u hu
      rw [(mem_filter.mp hu).2]
    _ = ∑ u ∈ range X, w u*S (u % d) := sum_fiberwise_of_maps_to hmaps _
    _ = _ := by
      apply sum_congr rfl
      intro u _
      simp only [S,mul_sum,sum_filter]
      apply sum_congr rfl
      intro v _
      by_cases h : v % d = u % d
      · simp [h]
      · simp [h,Ne.symm h]

end LagSquare

namespace LagSquare

open Finset

theorem positive (w : ℕ → ℝ) (X d : ℕ) (hd : 0 < d) :
    (∑ u ∈ range X, ∑ v ∈ (range X).filter (fun v => u<v ∧ u % d = v % d), w u*w v) =
      ∑ j ∈ Icc 1 ((X-1)/d), ∑ m ∈ range (X-d*j), w m*w (m+d*j) := by
  classical
  let pairs (u : ℕ) := (range X).filter (fun v : ℕ => u<v ∧ u % d = v % d)
  let lags (j : ℕ) := range (X-d*j)
  let B := (range X).sigma pairs
  let L := (Icc 1 ((X-1)/d)).sigma lags
  let decode (z : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨z.2, z.2+d*z.1⟩
  let encode (v : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨(v.2-v.1)/d, v.1⟩
  have hleft (z : Σ _ : ℕ, ℕ) : encode (decode z) = z := by
    rcases z with ⟨j,m⟩
    simp [encode, decode, Nat.mul_div_cancel_left _ hd]
  have hmap (z : Σ _ : ℕ, ℕ) (hz : z ∈ L) : decode z ∈ B := by
    obtain ⟨hJ,hM⟩ := mem_sigma.mp hz
    obtain ⟨hj,_⟩ := mem_Icc.mp hJ
    have hm := mem_range.mp hM
    have hpos : 0 < d*z.1 := Nat.mul_pos hd hj
    change z.2 < X-d*z.1 at hm
    apply mem_sigma.mpr
    refine ⟨mem_range.mpr (by change z.2 < X; omega), mem_filter.mpr ⟨?_, ?_⟩⟩
    · apply mem_range.mpr
      change z.2+d*z.1 < X
      omega
    · change z.2 < z.2+d*z.1 ∧ z.2 % d = (z.2+d*z.1) % d
      exact ⟨by omega, (Nat.add_mul_mod_self_left _ _ _).symm⟩
  have hsurj (v : Σ _ : ℕ, ℕ) (hv : v ∈ B) : encode v ∈ L ∧ decode (encode v)=v := by
    rcases v with ⟨u,v⟩
    obtain ⟨hu,hv⟩ := mem_sigma.mp hv
    obtain ⟨hv',huv,hm⟩ := mem_filter.mp hv
    change u < v at huv
    change u % d = v % d at hm
    have hx : v < X := mem_range.mp hv'
    have hdiv : d ∣ v-u := (Nat.modEq_iff_dvd' huv.le).mp hm
    have hprod := Nat.mul_div_cancel' hdiv
    have hpos : 0 < (v-u)/d := by
      by_contra! h
      rw [Nat.eq_zero_of_le_zero h, Nat.mul_zero] at hprod
      omega
    have hhigh : (v-u)/d ≤ (X-1)/d := Nat.div_le_div_right (by omega)
    refine ⟨mem_sigma.mpr ⟨mem_Icc.mpr ⟨hpos,hhigh⟩, mem_range.mpr ?_⟩, ?_⟩
    · change u < X-d*((v-u)/d)
      rw [hprod]
      omega
    · simp only [decode, encode, hprod, Nat.add_sub_of_le huv.le]
  change (∑ u ∈ range X, ∑ v ∈ pairs u, w u*w v) =
      ∑ j ∈ Icc 1 ((X-1)/d), ∑ m ∈ lags j, w m*w (m+d*j)
  rw [sum_sigma', sum_sigma']
  symm
  apply sum_bij (fun z _ => decode z) hmap
  · intro z _ z' _ he
    simpa only [hleft] using congrArg encode he
  · intro v hv
    exact ⟨encode v, (hsurj v hv).1, (hsurj v hv).2⟩
  · intro z _
    rfl

end LagSquare

namespace LagSquare
open Finset

private theorem diagonal_split (w : ℕ → ℝ) (X d : ℕ) :
    (∑ u ∈ range X, ∑ v ∈ range X, if u % d = v % d then w u * w v else 0) =
      (∑ u ∈ range X, (w u)^2) + 2 *
        (∑ u ∈ range X, ∑ v ∈ (range X).filter (fun v => u < v ∧ u % d = v % d),
          w u * w v) := by
  let P (u v : ℕ) : ℝ := if u < v ∧ u % d = v % d then w u * w v else 0
  have pair (u v : ℕ) :
      (if u % d = v % d then w u*w v else 0) =
        (if v = u then (w u)^2 else 0) + (P u v + P v u) := by
    rcases lt_trichotomy u v with h|rfl|h
    · by_cases e : u % d = v % d <;> simp [P, h, h.ne.symm, not_lt_of_ge h.le, e]
    · simp [P, sq]
    · by_cases e : u % d = v % d <;> simp [P, h, h.ne, not_lt_of_ge h.le, e, eq_comm (a := v % d), mul_comm]
  have diag : (∑ u ∈ range X, ∑ v ∈ range X, if v=u then (w u)^2 else 0) =
      ∑ u ∈ range X, (w u)^2 := by
    apply sum_congr rfl
    intro u hu
    simp [hu]
  have swap : (∑ u ∈ range X, ∑ v ∈ range X, P v u) =
      ∑ u ∈ range X, ∑ v ∈ range X, P u v := sum_comm
  simp_rw [pair, sum_add_distrib, diag, swap, sum_filter]
  change _ = _ + 2*(∑ u ∈ range X, ∑ v ∈ range X, P u v)
  ring

end LagSquare

theorem Conjectures.Cuts.Task99950cab5c8977334dbea5e5 : (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) => ∑ x4 ∈ Finset.range x3, (∑ x5 ∈ Finset.range x2 with x5 % x3 = x4, x1 x5) ^ (2 : ℕ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.Icc (1 : ℕ) ((x3 - (1 : ℕ)) / x4), ∑ x6 ∈ Finset.range (x3 - x4 * x5), x2 x6 * x2 (x6 + x4 * x5); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ), (0 : ℕ) < x5 → x1 x3 x4 x5 = ∑ x7 ∈ Finset.range x4, x3 x7 ^ (2 : ℕ) + (2 : ℝ) * x2 x3 x4 x5) := by
  intro A G w X d hd
  calc
    A w X d = _ := LagSquare.expand w X d hd
    _ = _ := LagSquare.diagonal_split w X d
    _ = _ := by rw [LagSquare.positive w X d hd]
