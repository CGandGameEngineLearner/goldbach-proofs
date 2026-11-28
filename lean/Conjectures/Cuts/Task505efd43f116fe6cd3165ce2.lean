import Mathlib

namespace Conjectures.Cuts.Task505efd43Proof

open scoped BigOperators

private lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (h0 : 0 ≤ f 0)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [(hd y).deriv]; exact hpos y (interior_subset hy))
  exact h0.trans (hmono Set.left_mem_Ici hx hx)

private lemma cos_ge_taylor2 {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 ≤ Real.cos x := by
  have h := nonneg_of_deriv_nonneg (f := fun t => Real.cos t - (1 - t ^ 2 / 2))
    (f' := fun t => t - Real.sin t)
    (by simp)
    (fun t => by
      have h1 := Real.hasDerivAt_cos t
      have h2 := ((hasDerivAt_pow 2 t).div_const 2).const_sub 1
      convert h1.sub h2 using 1
      ring)
    (fun t ht => by linarith [Real.sin_le ht])
    hx
  linarith

private lemma sin_ge_taylor3 {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have h := nonneg_of_deriv_nonneg (f := fun t => Real.sin t - (t - t ^ 3 / 6))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2))
    (by simp)
    (fun t => by
      have h1 := Real.hasDerivAt_sin t
      have h2 := (hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)
      convert h1.sub h2 using 1
      ring)
    (fun t ht => by linarith [cos_ge_taylor2 ht])
    hx
  linarith

private lemma cos_le_taylor4 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h := nonneg_of_deriv_nonneg (f := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t)
    (f' := fun t => Real.sin t - (t - t ^ 3 / 6))
    (by simp)
    (fun t => by
      have h1 := (((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add ((hasDerivAt_pow 4 t).div_const 24)
      have h2 := Real.hasDerivAt_cos t
      convert h1.sub h2 using 1
      ring)
    (fun t ht => by linarith [sin_ge_taylor3 ht])
    hx
  linarith

private lemma sin_le_taylor5 {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have h := nonneg_of_deriv_nonneg (f := fun t => (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t)
    (f' := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t)
    (by simp)
    (fun t => by
      have h1 := ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)
      have h2 := Real.hasDerivAt_sin t
      convert h1.sub h2 using 1
      ring)
    (fun t ht => by linarith [cos_le_taylor4 ht])
    hx
  linarith

private lemma cos_ge_taylor6 {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
    (f' := fun t => (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t)
    (by simp)
    (fun t => by
      have h1 := Real.hasDerivAt_cos t
      have h2 := ((((hasDerivAt_pow 2 t).div_const 2).const_sub 1).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)
      convert h1.sub h2 using 1
      ring)
    (fun t ht => by linarith [sin_le_taylor5 ht])
    hx
  linarith

private def flips8 (m : ℕ) : ℕ :=
  let b (j : ℕ) : ℕ := if j == 0 then 0 else (m / (2 ^ (8 - j))) % 2
  ((List.range 8).filter (fun j => b j != b (j + 1))).length

private def cosLBInt (m : ℕ) : ℤ :=
  if m < 128 then
    let u : ℕ := (3927 * (m + 1) + 31) / 32
    let u2 : ℕ := u * u
    let t2 : ℕ := (u2 + 199) / 200
    let t4 : ℕ := (u2 * u2) / 240000000000
    let t6 : ℕ := (u2 * u2 * u2 + 719999999999999999999) / 720000000000000000000
    (1000000 : ℤ) - (t2 : ℤ) + (t4 : ℤ) - (t6 : ℤ)
  else
    let v : ℕ := (62830 * (255 - m)) / 512
    let v2 : ℕ := v * v
    let t2 : ℕ := v2 / 200
    let t4 : ℕ := (v2 * v2 + 239999999999) / 240000000000
    (t2 : ℤ) - (1000000 : ℤ) - (t4 : ℤ)

private def w8Int (m : ℕ) : ℤ :=
  let f := flips8 m
  ((17 ^ f * 183 ^ (8 - f) : ℕ) : ℤ)

private def sumPow2 : ℕ → ℕ → (ℕ → ℤ) → ℤ
  | 0, a, f => f a
  | d + 1, a, f => sumPow2 d a f + sumPow2 d (a + 2 ^ d) f

private lemma sumPow2_eq_sum_Ico (d a : ℕ) (f : ℕ → ℤ) :
    sumPow2 d a f = ∑ m ∈ Finset.Ico a (a + 2 ^ d), f m := by
  induction d generalizing a with
  | zero => simp [sumPow2]
  | succ d ih =>
    simp only [sumPow2, ih]
    have hle1 : a ≤ a + 2 ^ d := Nat.le_add_right _ _
    have hle2 : a + 2 ^ d ≤ a + 2 ^ (d + 1) := by
      have : 2 ^ d ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d)
      omega
    have heq : a + 2 ^ d + 2 ^ d = a + 2 ^ (d + 1) := by ring
    rw [heq, Finset.sum_Ico_consecutive f hle1 hle2]

private lemma check_total_int :
    (7442 : ℤ) * (200 ^ 8 : ℕ) * 100 ≤ sumPow2 8 0 (fun m => w8Int m * cosLBInt m) := by
  decide

private lemma check_ent_nat :
    ((2 ^ 100) ^ 5 * 2 ^ 23) * (17 ^ 106) * ((183 ^ 104) ^ 11) < (200 ^ 125) ^ 10 := by
  decide

private lemma check_ent_real :
    ((17 / 200 : ℝ) ^ 212) * ((183 / 200 : ℝ) ^ 2288) ≤ ((2 : ℝ) ^ 1046)⁻¹ := by
  have hnat : 2 ^ 523 * 17 ^ 106 * 183 ^ 1144 < 200 ^ 1250 := by
    have h := check_ent_nat
    convert h using 1 <;> ring
  have hreal : (2 : ℝ) ^ 523 * 17 ^ 106 * 183 ^ 1144 ≤ 200 ^ 1250 := by
    exact_mod_cast hnat.le
  have hsq : ((2 : ℝ) ^ 523 * 17 ^ 106 * 183 ^ 1144) ^ 2 ≤ ((200 : ℝ) ^ 1250) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ 523 * 17 ^ 106 * 183 ^ 1144 by positivity]
  have h200 : (0 : ℝ) < (200 : ℝ) ^ 2500 := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ 1046 := by positivity
  rw [div_pow, div_pow, ← mul_div_mul_comm, ← pow_add, le_inv_iff_mul_le₀ h2]
  rw [div_mul_eq_mul_div, div_le_one h200]
  have h1 : ((2 : ℝ) ^ 523 * 17 ^ 106 * 183 ^ 1144) ^ 2 = (17 : ℝ) ^ 212 * 183 ^ 2288 * 2 ^ 1046 := by ring
  have h2' : ((200 : ℝ) ^ 1250) ^ 2 = (200 : ℝ) ^ 2500 := by ring
  linarith

private lemma nat_div_le_real (a b : ℕ) (hb : 0 < b) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)]
  exact_mod_cast Nat.div_mul_le_self a b

private lemma nat_ceil_div_ge_real (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (((a + (b - 1)) / b : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)]
  have h : a ≤ ((a + (b - 1)) / b) * b := by
    have h1 := Nat.div_add_mod (a + (b - 1)) b
    have h2 : (a + (b - 1)) % b < b := Nat.mod_lt _ hb
    omega
  exact_mod_cast h

private lemma cosLBInt_le_cos {m : ℕ} (hm : m < 256) {t : ℝ}
    (ht0 : (m : ℝ) / 512 ≤ t) (ht1 : t ≤ (m + 1 : ℝ) / 512) :
    (cosLBInt m : ℝ) / 1000000 ≤ Real.cos (2 * Real.pi * t) := by
  have hpi_lo : (31415 / 10000 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
  have hpi_hi : Real.pi < (31416 / 10000 : ℝ) := by linarith [Real.pi_lt_d4]
  have ht_nonneg : 0 ≤ t := by
    have : (0 : ℝ) ≤ (m : ℝ) / 512 := by positivity
    linarith
  have hm1_le : (m + 1 : ℝ) / 512 ≤ 1 / 2 := by
    have : (m : ℝ) + 1 ≤ 256 := by exact_mod_cast hm
    linarith
  have hcos_mono : Real.cos (2 * Real.pi * ((m + 1 : ℝ) / 512)) ≤ Real.cos (2 * Real.pi * t) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  refine le_trans ?_ hcos_mono
  unfold cosLBInt
  split_ifs with h128
  · set u : ℕ := (3927 * (m + 1) + 31) / 32
    have hu_ge : (3927 * ((m : ℝ) + 1)) / 32 ≤ (u : ℝ) := by
      have h := nat_ceil_div_ge_real (3927 * (m + 1)) 32 (by norm_num)
      push_cast at h
      exact h
    have hx_le : 2 * Real.pi * ((m + 1 : ℝ) / 512) ≤ (u : ℝ) / 10000 := by
      have : 2 * (31416 / 10000 : ℝ) * ((m + 1 : ℝ) / 512) = (3927 * ((m : ℝ) + 1)) / 32 / 10000 := by ring
      nlinarith
    have hu_le_pi : (u : ℝ) / 10000 ≤ Real.pi := by
      have hu_nat : u ≤ 15708 := by
        dsimp [u]
        omega
      have hu_r : (u : ℝ) ≤ 15708 := by exact_mod_cast hu_nat
      linarith
    have hcos_u : Real.cos ((u : ℝ) / 10000) ≤ Real.cos (2 * Real.pi * ((m + 1 : ℝ) / 512)) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · exact hu_le_pi
      · exact hx_le
    refine le_trans ?_ hcos_u
    have htay := cos_ge_taylor6 (show (0 : ℝ) ≤ (u : ℝ) / 10000 by positivity)
    refine le_trans ?_ htay
    have ht2 := nat_ceil_div_ge_real (u * u) 200 (by norm_num)
    have ht4 := nat_div_le_real (u * u * (u * u)) 240000000000 (by norm_num)
    have ht6 := nat_ceil_div_ge_real (u * u * (u * u) * (u * u)) 720000000000000000000 (by norm_num)
    push_cast at ht2 ht4 ht6 ⊢
    linarith
  · set v : ℕ := (62830 * (255 - m)) / 512
    have hm_ge : 128 ≤ m := Nat.le_of_not_lt h128
    have h255 : (255 - m : ℕ) + (m + 1) = 256 := by omega
    have h255_r : ((255 - m : ℕ) : ℝ) = 256 - ((m : ℝ) + 1) := by
      have : ((255 - m : ℕ) : ℝ) + ((m : ℝ) + 1) = 256 := by exact_mod_cast h255
      linarith
    have hcos_sym : Real.cos (2 * Real.pi * ((m + 1 : ℝ) / 512)) =
        -Real.cos (2 * Real.pi * (((255 - m : ℕ) : ℝ) / 512)) := by
      have harg : 2 * Real.pi * ((m + 1 : ℝ) / 512) =
          Real.pi - 2 * Real.pi * (((255 - m : ℕ) : ℝ) / 512) := by
        rw [h255_r]; ring
      rw [harg, Real.cos_pi_sub]
    rw [hcos_sym]
    have hv_le : (v : ℝ) / 10000 ≤ 2 * Real.pi * (((255 - m : ℕ) : ℝ) / 512) := by
      have h := nat_div_le_real (62830 * (255 - m)) 512 (by norm_num)
      push_cast at h
      have hnonneg : (0 : ℝ) ≤ ((255 - m : ℕ) : ℝ) := by positivity
      have heq : 2 * (31415 / 10000 : ℝ) * (((255 - m : ℕ) : ℝ) / 512) =
          (62830 * ((255 - m : ℕ) : ℝ) / 512) / 10000 := by ring
      nlinarith
    have harg_le_pi : 2 * Real.pi * (((255 - m : ℕ) : ℝ) / 512) ≤ Real.pi := by
      have hle : ((255 - m : ℕ) : ℝ) ≤ 256 := by exact_mod_cast (show 255 - m ≤ 256 by omega)
      nlinarith [Real.pi_pos]
    have hcos_v : Real.cos (2 * Real.pi * (((255 - m : ℕ) : ℝ) / 512)) ≤
        Real.cos ((v : ℝ) / 10000) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · exact harg_le_pi
      · exact hv_le
    have htay := cos_le_taylor4 (show (0 : ℝ) ≤ (v : ℝ) / 10000 by positivity)
    have hcos_ub : Real.cos (2 * Real.pi * (((255 - m : ℕ) : ℝ) / 512)) ≤
        1 - ((v : ℝ) / 10000) ^ 2 / 2 + ((v : ℝ) / 10000) ^ 4 / 24 :=
      hcos_v.trans htay
    have ht2 := nat_div_le_real (v * v) 200 (by norm_num)
    have ht4 := nat_ceil_div_ge_real (v * v * (v * v)) 240000000000 (by norm_num)
    push_cast at ht2 ht4 ⊢
    linarith

private lemma cosLBInt_le_cos_sym {m : ℕ} (hm : m < 512) {t : ℝ}
    (ht0 : (m : ℝ) / 512 ≤ t) (ht1 : t ≤ (m + 1 : ℝ) / 512) :
    (cosLBInt (if m < 256 then m else 511 - m) : ℝ) / 1000000 ≤ Real.cos (2 * Real.pi * t) := by
  split_ifs with h
  · exact cosLBInt_le_cos h ht0 ht1
  · have hge : 256 ≤ m := Nat.le_of_not_lt h
    have hm' : 511 - m < 256 := by omega
    have hsum : (511 - m : ℕ) + m = 511 := by omega
    have hsum_r : ((511 - m : ℕ) : ℝ) = 511 - (m : ℝ) := by
      have : ((511 - m : ℕ) : ℝ) + (m : ℝ) = 511 := by exact_mod_cast hsum
      linarith
    have hcos_eq : Real.cos (2 * Real.pi * t) = Real.cos (2 * Real.pi * (1 - t)) := by
      have harg : 2 * Real.pi * t = 2 * Real.pi - 2 * Real.pi * (1 - t) := by ring
      rw [harg, Real.cos_two_pi_sub]
    rw [hcos_eq]
    apply cosLBInt_le_cos hm'
    · rw [hsum_r]; linarith
    · rw [hsum_r]; linarith

-- Differential coordinates on length n+1 bitstrings: (b0 : Bool, d : Fin n → Bool)
private def bitAt {n : ℕ} (b0 : Bool) (d : Fin n → Bool) (i : ℕ) : Bool :=
  xor b0 (decide ((Finset.univ.filter (fun j : Fin n => j.1 < i ∧ d j = true)).card % 2 = 1))

private lemma bitAt_zero {n : ℕ} (b0 : Bool) (d : Fin n → Bool) : bitAt b0 d 0 = b0 := by
  simp [bitAt]

private lemma bitAt_succ {n : ℕ} (b0 : Bool) (d : Fin n → Bool) (i : Fin n) :
    bitAt b0 d (i.1 + 1) = xor (bitAt b0 d i.1) (d i) := by
  unfold bitAt
  have hset : Finset.univ.filter (fun j : Fin n => j.1 < i.1 + 1 ∧ d j = true) =
      (if d i = true then insert i (Finset.univ.filter (fun j : Fin n => j.1 < i.1 ∧ d j = true))
       else Finset.univ.filter (fun j : Fin n => j.1 < i.1 ∧ d j = true)) := by
    split_ifs with hdi
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hlt | heq
        · right; exact ⟨hlt, h2⟩
        · left; exact Fin.ext heq
      · rintro (rfl | ⟨hlt, h2⟩)
        · exact ⟨Nat.lt_succ_self _, hdi⟩
        · exact ⟨Nat.lt_succ_of_lt hlt, h2⟩
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hlt | heq
        · exact ⟨hlt, h2⟩
        · exfalso; exact hdi (by rwa [← Fin.ext heq])
      · intro ⟨hlt, h2⟩; exact ⟨Nat.lt_succ_of_lt hlt, h2⟩
  have hnotmem : i ∉ Finset.univ.filter (fun j : Fin n => j.1 < i.1 ∧ d j = true) := by
    simp
  rw [hset]
  cases hdi : d i
  · simp
  · simp only [↓reduceIte, Finset.card_insert_of_notMem hnotmem]
    cases b0 <;> simp <;> omega

private def toNatBits {n : ℕ} (b0 : Bool) (d : Fin n → Bool) : ℕ :=
  ∑ i : Fin (n + 1), if bitAt b0 d i.1 then 2 ^ (n - i.1) else 0

private lemma toNatBits_lt {n : ℕ} (b0 : Bool) (d : Fin n → Bool) :
    toNatBits b0 d < 2 ^ (n + 1) := by
  unfold toNatBits
  have hle : ∑ i : Fin (n + 1), (if bitAt b0 d i.1 then 2 ^ (n - i.1) else 0) ≤
      ∑ i : Fin (n + 1), 2 ^ (n - i.1) := by
    apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
  have hsum : ∑ i : Fin (n + 1), 2 ^ (n - i.1) = 2 ^ (n + 1) - 1 := by
    have h1 : ∑ i : Fin (n + 1), 2 ^ (n - i.1) = ∑ i ∈ Finset.range (n + 1), 2 ^ i := by
      rw [Fin.sum_univ_eq_sum_range (fun k => 2 ^ (n - k))]
      rw [← Finset.sum_range_reflect (fun k => 2 ^ k) (n + 1)]
      apply Finset.sum_congr rfl
      intro x hx
      have : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      have : n + 1 - 1 - x = n - x := by omega
      rw [this]
    rw [h1]
    have hgeom := Nat.geomSum_eq (show 2 ≤ 2 by norm_num) (n + 1)
    simpa using hgeom
  have hpos : 0 < 2 ^ (n + 1) := by positivity
  omega

private lemma toNatBits_injective {n : ℕ} :
    Function.Injective (fun x : Bool × (Fin n → Bool) => toNatBits x.1 x.2) := by
  intro ⟨b1, d1⟩ ⟨b2, d2⟩ h
  have hbits : ∀ i : Fin (n + 1), bitAt b1 d1 i.1 = bitAt b2 d2 i.1 := by
    intro i
    -- Prove by strong induction on i.1 using the binary expansion
    induction hi : i.1 using Nat.strong_induction_on generalizing i with
    | _ k ih =>
      have hprefix : ∀ j : Fin (n + 1), j.1 < k → bitAt b1 d1 j.1 = bitAt b2 d2 j.1 :=
        fun j hj => ih j.1 hj j rfl
      have htail : ∀ (b : Bool) (d : Fin n → Bool),
          ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k < j.1),
            (if bitAt b d j.1 then 2 ^ (n - j.1) else 0) < 2 ^ (n - k) := by
        intro b d
        have hle : ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k < j.1),
            (if bitAt b d j.1 then 2 ^ (n - j.1) else 0) ≤
            ∑ j ∈ Finset.range (n - k), 2 ^ j := by
          have h1 : ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k < j.1),
              (if bitAt b d j.1 then 2 ^ (n - j.1) else 0) ≤
              ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k < j.1), 2 ^ (n - j.1) := by
            apply Finset.sum_le_sum; intro j _; split_ifs <;> omega
          refine h1.trans (le_of_eq ?_)
          apply Finset.sum_nbij (fun j => n - j.1)
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            simp only [Finset.mem_range]; omega
          · intro j1 hj1 j2 hj2 heq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
            exact Fin.ext (by omega)
          · intro r hr
            simp only [Finset.mem_range] at hr
            refine ⟨⟨n - r, by omega⟩, ?_, by omega⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
          · intro _ _; rfl
        have hgeom : ∑ j ∈ Finset.range (n - k), 2 ^ j = 2 ^ (n - k) - 1 := by
          simpa using Nat.geomSum_eq (show 2 ≤ 2 by norm_num) (n - k)
        have hpos : 0 < 2 ^ (n - k) := by positivity
        omega
      have hsplit : ∀ (b : Bool) (d : Fin n → Bool),
          toNatBits b d =
            (∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.1 < k),
              if bitAt b d j.1 then 2 ^ (n - j.1) else 0) +
            (if bitAt b d k then 2 ^ (n - k) else 0) +
            (∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => k < j.1),
              if bitAt b d j.1 then 2 ^ (n - j.1) else 0) := by
        intro b d
        unfold toNatBits
        have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin (n + 1) => j.1 < k)
          (fun j => if bitAt b d j.1 then 2 ^ (n - j.1) else 0)).symm
        rw [h1]
        have h2 := (Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun j : Fin (n + 1) => ¬ j.1 < k))
          (fun j : Fin (n + 1) => j.1 = k)
          (fun j => if bitAt b d j.1 then 2 ^ (n - j.1) else 0)).symm
        rw [h2, ← add_assoc]
        congr 1
        · congr 1
          have hsing : (Finset.univ.filter (fun j : Fin (n + 1) => ¬ j.1 < k)).filter
              (fun j : Fin (n + 1) => j.1 = k) = {i} := by
            ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro ⟨_, heq⟩; exact Fin.ext (by omega)
            · rintro rfl; omega
          rw [hsing, Finset.sum_singleton, hi]
        · apply Finset.sum_congr
          · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
          · intro _ _; rfl
      have hs1 := hsplit b1 d1
      have hs2 := hsplit b2 d2
      have hpre_eq : ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.1 < k),
          (if bitAt b1 d1 j.1 then 2 ^ (n - j.1) else 0) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.1 < k),
          (if bitAt b2 d2 j.1 then 2 ^ (n - j.1) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hprefix j (Finset.mem_filter.mp hj).2]
      have ht1 := htail b1 d1
      have ht2 := htail b2 d2
      rw [hi]
      cases hb1 : bitAt b1 d1 k <;> cases hb2 : bitAt b2 d2 k
      · rfl
      · simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte] at hs1 hs2; omega
      · simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte] at hs1 hs2; omega
      · rfl
  have hb0 : b1 = b2 := by
    have := hbits ⟨0, Nat.zero_lt_succ n⟩
    simpa [bitAt_zero] using this
  subst hb0
  congr 1
  ext j
  have h1 := hbits ⟨j.1, by omega⟩
  have h2 := hbits ⟨j.1 + 1, by omega⟩
  rw [bitAt_succ, bitAt_succ, h1] at h2
  cases bitAt b1 d2 j.1 <;> cases d1 j <;> cases d2 j <;> simp_all

-- Extract the 9-bit window starting at position k (when k + 9 ≤ n + 1)
private def window9 {n : ℕ} (b0 : Bool) (d : Fin n → Bool) (k : ℕ) : ℕ :=
  ∑ j : Fin 9, if bitAt b0 d (k + j.1) then 2 ^ (8 - j.1) else 0

private lemma window9_lt {n : ℕ} (b0 : Bool) (d : Fin n → Bool) (k : ℕ) :
    window9 b0 d k < 512 := by
  unfold window9
  have hle : ∑ j : Fin 9, (if bitAt b0 d (k + j.1) then 2 ^ (8 - j.1) else 0) ≤
      ∑ j : Fin 9, 2 ^ (8 - j.1) := by
    apply Finset.sum_le_sum; intro j _; split_ifs <;> omega
  have h511 : ∑ j : Fin 9, 2 ^ (8 - j.1) = 511 := by decide
  omega

private lemma floor_phase_window9 {n : ℕ} (b0 : Bool) (d : Fin n → Bool) {k : ℕ}
    (hk : k + 9 ≤ n + 1) :
    ∃ (z : ℤ) (t : ℝ),
      (window9 b0 d k : ℝ) / 512 ≤ t ∧
      t ≤ ((window9 b0 d k : ℝ) + 1) / 512 ∧
      (⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits b0 d : ℝ) / (2 : ℝ) ^ (n + 1))⌋ : ℝ) / 65536 =
        (z : ℝ) + t := by
  let W := toNatBits b0 d
  let high : ℕ := ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.1 < k),
    if bitAt b0 d i.1 then 2 ^ (k - 1 - i.1) else 0
  let mid : ℕ := window9 b0 d k
  let low : ℕ := ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => k + 9 ≤ i.1),
    if bitAt b0 d i.1 then 2 ^ (n - i.1) else 0
  have hW : W = high * 2 ^ (n + 1 - k) + mid * 2 ^ (n + 1 - k - 9) + low := by
    dsimp [W, toNatBits, high, mid, window9, low]
    have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (n + 1) => i.1 < k)
      (fun i => if bitAt b0 d i.1 then 2 ^ (n - i.1) else 0)).symm
    rw [h1]
    have h2 := (Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun i : Fin (n + 1) => ¬ i.1 < k))
      (fun i : Fin (n + 1) => i.1 < k + 9)
      (fun i => if bitAt b0 d i.1 then 2 ^ (n - i.1) else 0)).symm
    rw [h2, ← add_assoc]
    congr 1
    · congr 1
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        have hik : i.1 < k := (Finset.mem_filter.mp hi).2
        split_ifs
        · rw [← pow_add]; congr 1; omega
        · simp
      · rw [Finset.sum_mul]
        apply Finset.sum_bij (fun i hi => (⟨i.1 - k, by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            omega⟩ : Fin 9))
        · intro _ _; simp
        · intro i1 hi1 i2 hi2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
          have hval : i1.1 - k = i2.1 - k := congrArg Fin.val heq
          exact Fin.ext (by omega)
        · intro j _
          refine ⟨⟨k + j.1, by omega⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
          · exact Fin.ext (by omega)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hki : k + (i.1 - k) = i.1 := by omega
          rw [hki]
          split_ifs
          · rw [← pow_add]; congr 1; omega
          · simp
    · apply Finset.sum_congr
      · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · intro _ _; rfl
  have hlow_lt : low < 2 ^ (n + 1 - k - 9) := by
    dsimp [low]
    have hle : ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => k + 9 ≤ i.1),
        (if bitAt b0 d i.1 then 2 ^ (n - i.1) else 0) ≤
        ∑ j ∈ Finset.range (n + 1 - k - 9), 2 ^ j := by
      have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => k + 9 ≤ i.1),
          (if bitAt b0 d i.1 then 2 ^ (n - i.1) else 0) ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => k + 9 ≤ i.1), 2 ^ (n - i.1) := by
        apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
      refine h1.trans (le_of_eq ?_)
      apply Finset.sum_nbij (fun i => n - i.1)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_range]; omega
      · intro i1 hi1 i2 hi2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
        exact Fin.ext (by omega)
      · intro r hr
        simp only [Finset.mem_range] at hr
        refine ⟨⟨n - r, by omega⟩, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · intro _ _; rfl
    have hgeom : ∑ j ∈ Finset.range (n + 1 - k - 9), 2 ^ j = 2 ^ (n + 1 - k - 9) - 1 := by
      simpa using Nat.geomSum_eq (show 2 ≤ 2 by norm_num) (n + 1 - k - 9)
    have hpos : 0 < 2 ^ (n + 1 - k - 9) := by positivity
    omega
  set s := n + 1 - k - 9
  have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ k * 512 * (2 : ℝ) ^ s := by
    have h512 : (512 : ℝ) = (2 : ℝ) ^ 9 := by norm_num
    rw [h512, ← pow_add, ← pow_add]
    congr 1; omega
  have hpow2 : (2 : ℝ) ^ (n + 1 - k) = 512 * (2 : ℝ) ^ s := by
    have h512 : (512 : ℝ) = (2 : ℝ) ^ 9 := by norm_num
    rw [h512, ← pow_add]
    congr 1; omega
  have hval : (65536 : ℝ) * (2 : ℝ) ^ k * ((W : ℝ) / (2 : ℝ) ^ (n + 1)) =
      (65536 : ℝ) * (high : ℝ) + (128 : ℝ) * (mid : ℝ) + (128 : ℝ) * (low : ℝ) / (2 : ℝ) ^ s := by
    rw [hW, hpow]
    push_cast
    rw [hpow2]
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    have h2s : (2 : ℝ) ^ s ≠ 0 := by positivity
    field_simp
    ring
  have hlow_r0 : (0 : ℝ) ≤ (128 : ℝ) * (low : ℝ) / (2 : ℝ) ^ s := by positivity
  have hlow_r1 : (128 : ℝ) * (low : ℝ) / (2 : ℝ) ^ s < 128 := by
    have hlow_lt_r : (low : ℝ) < (2 : ℝ) ^ s := by exact_mod_cast hlow_lt
    have h2s : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    rw [div_lt_iff₀ h2s]
    linarith
  set fl : ℤ := ⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((W : ℝ) / (2 : ℝ) ^ (n + 1))⌋
  have hfl_ge : ((65536 * high + 128 * mid : ℕ) : ℤ) ≤ fl := by
    dsimp [fl]
    rw [Int.le_floor, hval]
    push_cast
    linarith
  have hfl_lt : fl < ((65536 * high + 128 * mid + 128 : ℕ) : ℤ) := by
    dsimp [fl]
    rw [Int.floor_lt, hval]
    push_cast
    linarith
  refine ⟨(high : ℤ), (fl : ℝ) / 65536 - (high : ℝ), ?_, ?_, ?_⟩
  · have hge : (65536 : ℝ) * (high : ℝ) + 128 * (mid : ℝ) ≤ (fl : ℝ) := by
      have : ((65536 * high + 128 * mid : ℕ) : ℝ) ≤ (fl : ℝ) := by exact_mod_cast hfl_ge
      push_cast at this; linarith
    linarith
  · have hlt : (fl : ℝ) ≤ (65536 : ℝ) * (high : ℝ) + 128 * (mid : ℝ) + 128 := by
      have : (fl : ℝ) < ((65536 * high + 128 * mid + 128 : ℕ) : ℝ) := by exact_mod_cast hfl_lt
      push_cast at this; linarith
    linarith
  · ring

private lemma term_re_ge_cosLB {n : ℕ} (b0 : Bool) (d : Fin n → Bool) {k : ℕ}
    (hk : k + 9 ≤ n + 1) :
    (cosLBInt (let m := window9 b0 d k; if m < 256 then m else 511 - m) : ℝ) / 1000000 ≤
      (Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits b0 d : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re := by
  rw [Complex.exp_ofReal_mul_I_re]
  obtain ⟨z, t, ht0, ht1, heq⟩ := floor_phase_window9 b0 d hk
  have harg : (2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits b0 d : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ) =
      2 * Real.pi * t + (z : ℝ) * (2 * Real.pi) := by
    have h1 : (2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits b0 d : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ) =
        2 * Real.pi * ((↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits b0 d : ℝ) / (2 : ℝ) ^ (n + 1))⌋ : ℝ) / 65536) := by ring
    rw [h1, heq]; ring
  rw [harg, Real.cos_add_int_mul_two_pi]
  exact cosLBInt_le_cos_sym (window9_lt b0 d k) ht0 ht1

-- Probability weights on differential coordinates
private noncomputable def qR : ℝ := 17 / 200
private noncomputable def wBool (b : Bool) : ℝ := if b then qR else 1 - qR
private noncomputable def pDiff {n : ℕ} (d : Fin n → Bool) : ℝ := ∏ j : Fin n, wBool (d j)
private noncomputable def pState {n : ℕ} (x : Bool × (Fin n → Bool)) : ℝ := (1 / 2 : ℝ) * pDiff x.2

private lemma wBool_nonneg (b : Bool) : 0 ≤ wBool b := by
  cases b <;> simp [wBool, qR] <;> norm_num

private lemma pDiff_nonneg {n : ℕ} (d : Fin n → Bool) : 0 ≤ pDiff d :=
  Finset.prod_nonneg (fun j _ => wBool_nonneg (d j))

private lemma pState_nonneg {n : ℕ} (x : Bool × (Fin n → Bool)) : 0 ≤ pState x :=
  mul_nonneg (by norm_num) (pDiff_nonneg x.2)

private lemma sum_wBool : ∑ b : Bool, wBool b = 1 := by
  simp [wBool, qR]; ring

private lemma sum_pDiff (n : ℕ) : ∑ d : Fin n → Bool, pDiff d = 1 := by
  unfold pDiff
  rw [← Fintype.prod_sum]
  simp [sum_wBool]

private lemma sum_pState (n : ℕ) : ∑ x : Bool × (Fin n → Bool), pState x = 1 := by
  unfold pState
  rw [Fintype.sum_prod_type]
  simp [← Finset.mul_sum, sum_pDiff]
  ring

-- Relate window9 to differential bits (d_k, ..., d_{k+7})
private def maskFromDiff8 (d8 : Fin 8 → Bool) : ℕ :=
  ∑ j : Fin 8,
    if decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 ∧ d8 i = true)).card % 2 = 1)
    then 2 ^ (7 - j.1) else 0

private lemma maskFromDiff8_lt (d8 : Fin 8 → Bool) : maskFromDiff8 d8 < 256 := by
  unfold maskFromDiff8
  have hle : ∑ j : Fin 8, (if decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 ∧ d8 i = true)).card % 2 = 1)
      then 2 ^ (7 - j.1) else 0) ≤ ∑ j : Fin 8, 2 ^ (7 - j.1) := by
    apply Finset.sum_le_sum; intro j _; split_ifs <;> omega
  have h255 : ∑ j : Fin 8, 2 ^ (7 - j.1) = 255 := by decide
  omega

private lemma window9_reduced_eq {n : ℕ} (b0 : Bool) (d : Fin n → Bool) {k : ℕ}
    (hk : k + 9 ≤ n + 1) :
    (let m := window9 b0 d k; if m < 256 then m else 511 - m) =
      maskFromDiff8 (fun j : Fin 8 => d ⟨k + j.1, by omega⟩) := by
  let bk := bitAt b0 d k
  let d8 : Fin 8 → Bool := fun j => d ⟨k + j.1, by omega⟩
  have hbit_rel : ∀ j : Fin 9,
      bitAt b0 d (k + j.1) = xor bk
        (if j.1 = 0 then false
         else decide ((Finset.univ.filter (fun i : Fin 8 => i.1 < j.1 ∧ d8 i = true)).card % 2 = 1)) := by
    intro ⟨j, hj⟩
    induction j with
    | zero => simp [bk]
    | succ j ih =>
      have hj9 : j < 9 := by omega
      have hprev := ih hj9
      have hstep := bitAt_succ b0 d ⟨k + j, by omega⟩
      have hkj : k + (j + 1) = (k + j) + 1 := by omega
      rw [hkj, hstep, hprev]
      have hj8 : j < 8 := by omega
      let fj : Fin 8 := ⟨j, hj8⟩
      have hset : Finset.univ.filter (fun i : Fin 8 => i.1 < j + 1 ∧ d8 i = true) =
          (if d8 fj = true then insert fj (Finset.univ.filter (fun i : Fin 8 => i.1 < j ∧ d8 i = true))
           else Finset.univ.filter (fun i : Fin 8 => i.1 < j ∧ d8 i = true)) := by
        split_ifs with hdj
        · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro ⟨h1, h2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hlt | heq
            · right; exact ⟨hlt, h2⟩
            · left; exact Fin.ext heq
          · rintro (rfl | ⟨hlt, h2⟩)
            · exact ⟨Nat.lt_succ_self _, hdj⟩
            · exact ⟨Nat.lt_succ_of_lt hlt, h2⟩
        · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro ⟨h1, h2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hlt | heq
            · exact ⟨hlt, h2⟩
            · exfalso; exact hdj (by rwa [← Fin.ext heq])
          · intro ⟨hlt, h2⟩; exact ⟨Nat.lt_succ_of_lt hlt, h2⟩
      have hnotmem : fj ∉ Finset.univ.filter (fun i : Fin 8 => i.1 < j ∧ d8 i = true) := by simp [fj]
      have hd_eq : d ⟨k + j, by omega⟩ = d8 fj := rfl
      rw [hd_eq, hset]
      cases j with
      | zero =>
        cases hdj : d8 fj <;> cases bk <;> simp [fj]
      | succ j' =>
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        cases hdj : d8 fj
        · simp
        · simp only [↓reduceIte, Finset.card_insert_of_notMem hnotmem]
          cases bk <;> simp <;> omega
  have hmask_eq : ∀ b : Bool,
      window9 b0 d k = (if bk then 511 - maskFromDiff8 d8 else maskFromDiff8 d8) := by
    intro _
    unfold window9 maskFromDiff8
    rw [Fin.sum_univ_succ]
    have h0 := hbit_rel 0
    simp only [Fin.val_zero, add_zero, ↓reduceIte, Bool.xor_false] at h0
    rw [h0]
    have htail : ∀ j : Fin 8,
        bitAt b0 d (k + (j.succ).1) = xor bk
          (decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 ∧ d8 i = true)).card % 2 = 1)) := by
      intro j
      have := hbit_rel j.succ
      simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte] at this
      rw [this]
      congr 2; congr 1; congr 1
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    cases hbk : bk
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      apply Finset.sum_congr rfl
      intro j _
      rw [htail j, hbk, Bool.false_xor]
      have : 8 - (j.succ).1 = 7 - j.1 := by omega
      rw [this]
    · simp only [↓reduceIte]
      have hsum255 : ∑ j : Fin 8, 2 ^ (7 - j.1) = 255 := by decide
      have hcomp : (∑ j : Fin 8, if bitAt b0 d (k + (j.succ).1) then 2 ^ (8 - (j.succ).1) else 0) +
          (∑ j : Fin 8, if decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 ∧ d8 i = true)).card % 2 = 1)
            then 2 ^ (7 - j.1) else 0) = 255 := by
        rw [← Finset.sum_add_distrib, ← hsum255]
        apply Finset.sum_congr rfl
        intro j _
        rw [htail j, hbk, Bool.true_xor]
        have : 8 - (j.succ).1 = 7 - j.1 := by omega
        rw [this]
        cases decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 ∧ d8 i = true)).card % 2 = 1) <;> simp
      have hlt := maskFromDiff8_lt d8
      dsimp only [maskFromDiff8] at hlt
      omega
  have hm_eq := hmask_eq false
  have hlt := maskFromDiff8_lt d8
  rw [hm_eq]
  cases bk
  · simp [hlt]
  · have hge : ¬ (511 - maskFromDiff8 d8 < 256) := by omega
    simp [hge]
    omega

private lemma flips8_maskFromDiff8 (d8 : Fin 8 → Bool) :
    flips8 (maskFromDiff8 d8) = (Finset.univ.filter (fun j : Fin 8 => d8 j = true)).card := by
  have hbit : ∀ j : ℕ, j < 8 →
      (maskFromDiff8 d8 / 2 ^ (7 - j)) % 2 =
        if decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j ∧ d8 i = true)).card % 2 = 1)
        then 1 else 0 := by
    intro j hj
    let c (r : ℕ) : ℕ :=
      if hr : r < 8 then
        if decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ r ∧ d8 i = true)).card % 2 = 1) then 1 else 0
      else 0
    have hsplit : maskFromDiff8 d8 =
        (∑ i ∈ Finset.univ.filter (fun i : Fin 8 => i.1 < j), c i.1 * 2 ^ (j - 1 - i.1)) * 2 ^ (8 - j) +
        c j * 2 ^ (7 - j) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin 8 => j < i.1), c i.1 * 2 ^ (7 - i.1)) := by
      unfold maskFromDiff8
      have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin 8 => i.1 < j)
        (fun i => if decide ((Finset.univ.filter (fun r : Fin 8 => r.1 ≤ i.1 ∧ d8 r = true)).card % 2 = 1)
          then 2 ^ (7 - i.1) else 0)).symm
      rw [h1]
      have h2 := (Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun i : Fin 8 => ¬ i.1 < j))
        (fun i : Fin 8 => i.1 = j)
        (fun i => if decide ((Finset.univ.filter (fun r : Fin 8 => r.1 ≤ i.1 ∧ d8 r = true)).card % 2 = 1)
          then 2 ^ (7 - i.1) else 0)).symm
      rw [h2, ← add_assoc]
      congr 1
      · congr 1
        · rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          have hij : i.1 < j := (Finset.mem_filter.mp hi).2
          have hi8 : i.1 < 8 := i.2
          dsimp [c]; simp only [hi8, ↓reduceDIte]
          split_ifs
          · rw [one_mul, ← pow_add]; congr 1; omega
          · simp
        · have hsing : (Finset.univ.filter (fun i : Fin 8 => ¬ i.1 < j)).filter
              (fun i : Fin 8 => i.1 = j) = {⟨j, hj⟩} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro ⟨_, heq⟩; exact Fin.ext heq
            · rintro rfl; omega
          rw [hsing, Finset.sum_singleton]
          dsimp [c]; simp only [hj, ↓reduceDIte]
          split_ifs <;> simp
      · apply Finset.sum_congr
        · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
        · intro i _
          dsimp [c]; simp only [i.2, ↓reduceDIte]
          split_ifs <;> simp
    have hlow : ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => j < i.1), c i.1 * 2 ^ (7 - i.1) < 2 ^ (7 - j) := by
      have hle : ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => j < i.1), c i.1 * 2 ^ (7 - i.1) ≤
          ∑ r ∈ Finset.range (7 - j), 2 ^ r := by
        have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => j < i.1), c i.1 * 2 ^ (7 - i.1) ≤
            ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => j < i.1), 2 ^ (7 - i.1) := by
          apply Finset.sum_le_sum; intro i _
          have hc : c i.1 ≤ 1 := by dsimp [c]; split_ifs <;> omega
          nlinarith
        refine h1.trans (le_of_eq ?_)
        apply Finset.sum_nbij (fun i => 7 - i.1)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp only [Finset.mem_range]; omega
        · intro i1 hi1 i2 hi2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
          exact Fin.ext (by omega)
        · intro r hr
          simp only [Finset.mem_range] at hr
          refine ⟨⟨7 - r, by omega⟩, ?_, by omega⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
        · intro _ _; rfl
      have hgeom : ∑ r ∈ Finset.range (7 - j), 2 ^ r = 2 ^ (7 - j) - 1 := by
        simpa using Nat.geomSum_eq (show 2 ≤ 2 by norm_num) (7 - j)
      have hpos : 0 < 2 ^ (7 - j) := by positivity
      omega
    have hpow : 2 ^ (8 - j) = 2 * 2 ^ (7 - j) := by
      have : 8 - j = (7 - j) + 1 := by omega
      rw [this, pow_succ, mul_comm]
    rw [hsplit, hpow]
    set A := ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => i.1 < j), c i.1 * 2 ^ (j - 1 - i.1)
    set B := ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => j < i.1), c i.1 * 2 ^ (7 - i.1)
    have hpos : 0 < 2 ^ (7 - j) := by positivity
    have hdiv : (A * (2 * 2 ^ (7 - j)) + c j * 2 ^ (7 - j) + B) / 2 ^ (7 - j) = 2 * A + c j := by
      have heq : A * (2 * 2 ^ (7 - j)) + c j * 2 ^ (7 - j) + B = B + (2 * A + c j) * 2 ^ (7 - j) := by ring
      rw [heq, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlow, zero_add]
    rw [hdiv]
    have hcj : c j = if decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j ∧ d8 i = true)).card % 2 = 1) then 1 else 0 := by
      dsimp [c]; simp only [hj, ↓reduceDIte]
    rw [hcj]
    split_ifs <;> omega
  unfold flips8
  have hlen : ((List.range 8).filter (fun j =>
      (if j == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - j)) % 2) !=
      (if j + 1 == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - (j + 1))) % 2))).length =
      (Finset.univ.filter (fun j : Fin 8 => d8 j = true)).card := by
    have hpred : ∀ j : Fin 8,
        ((if j.1 == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - j.1)) % 2) !=
         (if j.1 + 1 == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - (j.1 + 1))) % 2)) = d8 j := by
      intro j
      have h1 : (if j.1 + 1 == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - (j.1 + 1))) % 2) =
          if decide ((Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 ∧ d8 i = true)).card % 2 = 1)
          then 1 else 0 := by
        have hnz : (j.1 + 1 == 0) = false := by simp
        have hsub : 8 - (j.1 + 1) = 7 - j.1 := by omega
        rw [hnz, hsub]
        exact hbit j.1 j.2
      rw [h1]
      rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
      · have hjeq : j = 0 := Fin.ext hj0
        subst hjeq
        have hset : Finset.univ.filter (fun i : Fin 8 => i.1 ≤ 0 ∧ d8 i = true) =
            if d8 0 = true then {0} else ∅ := by
          split_ifs with h0
          · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro ⟨h1, _⟩; exact Fin.ext (by omega)
            · rintro rfl; exact ⟨le_rfl, h0⟩
          · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            intro ⟨h1, h2⟩; exact h0 (by rwa [← Fin.ext (show i.1 = 0 by omega)])
        rw [hset]
        cases d8 0 <;> simp
      · have hnz : (j.1 == 0) = false := by simp; omega
        have hsub : 8 - j.1 = 7 - (j.1 - 1) := by omega
        rw [hnz, hsub, hbit (j.1 - 1) (by omega)]
        have hset : Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 ∧ d8 i = true) =
            if d8 j = true then insert j (Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 - 1 ∧ d8 i = true))
            else Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 - 1 ∧ d8 i = true) := by
          split_ifs with hdj
          · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · intro ⟨h1, h2⟩
              rcases lt_or_eq_of_le h1 with hlt | heq
              · right; exact ⟨by omega, h2⟩
              · left; exact Fin.ext heq
            · rintro (rfl | ⟨hle, h2⟩)
              · exact ⟨le_rfl, hdj⟩
              · exact ⟨by omega, h2⟩
          · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro ⟨h1, h2⟩
              rcases lt_or_eq_of_le h1 with hlt | heq
              · exact ⟨by omega, h2⟩
              · exfalso; exact hdj (by rwa [← Fin.ext heq])
            · intro ⟨hle, h2⟩; exact ⟨by omega, h2⟩
        have hnm : j ∉ Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 - 1 ∧ d8 i = true) := by
          simp; omega
        rw [hset]
        cases hdj : d8 j
        · simp
        · simp only [↓reduceIte, Finset.card_insert_of_notMem hnm]
          set c := (Finset.univ.filter (fun i : Fin 8 => i.1 ≤ j.1 - 1 ∧ d8 i = true)).card
          by_cases hc : c % 2 = 1 <;> simp [hc] <;> omega
    have h1 : ((List.range 8).filter (fun j =>
        (if j == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - j)) % 2) !=
        (if j + 1 == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - (j + 1))) % 2))).length =
        (Finset.univ.filter (fun j : Fin 8 =>
          (if j.1 == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - j.1)) % 2) !=
          (if j.1 + 1 == 0 then 0 else (maskFromDiff8 d8 / 2 ^ (8 - (j.1 + 1))) % 2))).card := by
      rw [← List.card_toFinset]
      · apply Finset.card_bij (fun a ha => ⟨a, by
          have := List.mem_filter.mp (List.mem_toFinset.mp ha)
          exact List.mem_range.mp this.1⟩)
        · intro a ha
          have := List.mem_filter.mp (List.mem_toFinset.mp ha)
          simp [this.2]
        · intro a1 _ a2 _ heq; exact congrArg Fin.val heq
        · intro b hb
          refine ⟨b.1, ?_, Fin.ext rfl⟩
          rw [List.mem_toFinset, List.mem_filter, List.mem_range]
          exact ⟨b.2, (Finset.mem_filter.mp hb).2⟩
      · exact (List.nodup_range).filter _
    rw [h1]
    congr 1; ext j; simp [hpred j]
  exact hlen

private lemma maskFromDiff8_eq_toNatBits (d8 : Fin 8 → Bool) :
    maskFromDiff8 d8 = toNatBits false d8 := by
  unfold maskFromDiff8 toNatBits
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, bitAt_zero, Bool.false_eq_true, ↓reduceIte, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  have hsub : 8 - (i.succ).1 = 7 - i.1 := by omega
  rw [hsub]
  unfold bitAt
  simp only [Bool.false_xor]
  congr 2; congr 1; congr 1
  ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ]; omega

private lemma maskFromDiff8_bijective :
    Function.Bijective (fun d8 : Fin 8 → Bool => (⟨maskFromDiff8 d8, maskFromDiff8_lt d8⟩ : Fin 256)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro d1 d2 heq
  have hval : maskFromDiff8 d1 = maskFromDiff8 d2 := congrArg Fin.val heq
  rw [maskFromDiff8_eq_toNatBits, maskFromDiff8_eq_toNatBits] at hval
  have hpair := toNatBits_injective hval
  exact congrArg Prod.snd hpair

private lemma pDiff_eq_w8Int (d8 : Fin 8 → Bool) :
    pDiff d8 = (w8Int (maskFromDiff8 d8) : ℝ) / (200 : ℝ) ^ 8 := by
  unfold pDiff wBool qR w8Int
  rw [flips8_maskFromDiff8]
  set f := (Finset.univ.filter (fun j : Fin 8 => d8 j = true)).card
  have hprod : ∏ j : Fin 8, (if d8 j = true then (17 / 200 : ℝ) else 1 - 17 / 200) =
      (17 / 200 : ℝ) ^ f * (183 / 200 : ℝ) ^ (8 - f) := by
    have h1 : ∀ j : Fin 8, (if d8 j = true then (17 / 200 : ℝ) else 1 - 17 / 200) =
        if d8 j = true then (17 / 200 : ℝ) else (183 / 200 : ℝ) := by
      intro j; split_ifs <;> norm_num
    simp_rw [h1]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hcomp : (Finset.univ.filter (fun j : Fin 8 => ¬ d8 j = true)).card = 8 - f := by
      have htot := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin 8)))
        (p := fun j => d8 j = true)
      simp only [Finset.card_univ, Fintype.card_fin] at htot
      omega
    rw [hcomp]
  rw [hprod]
  have hf_le : f ≤ 8 := by
    calc f ≤ (Finset.univ : Finset (Fin 8)).card := Finset.card_filter_le _ _
      _ = 8 := by simp
  rw [div_pow, div_pow, ← mul_div_mul_comm, ← pow_add, Nat.add_sub_of_le hf_le]
  push_cast
  rfl

private lemma sum_pDiff_cosLB8 :
    (7442 / 10000 : ℝ) ≤
      ∑ d8 : Fin 8 → Bool, pDiff d8 * ((cosLBInt (maskFromDiff8 d8) : ℝ) / 1000000) := by
  have hre : ∑ d8 : Fin 8 → Bool, pDiff d8 * ((cosLBInt (maskFromDiff8 d8) : ℝ) / 1000000) =
      (∑ m : Fin 256, ((w8Int m.1 * cosLBInt m.1 : ℤ) : ℝ)) / ((200 : ℝ) ^ 8 * 1000000) := by
    have hstep1 : ∑ d8 : Fin 8 → Bool, pDiff d8 * ((cosLBInt (maskFromDiff8 d8) : ℝ) / 1000000) =
        ∑ d8 : Fin 8 → Bool, ((w8Int (maskFromDiff8 d8) * cosLBInt (maskFromDiff8 d8) : ℤ) : ℝ) / ((200 : ℝ) ^ 8 * 1000000) := by
      apply Finset.sum_congr rfl
      intro d8 _
      rw [pDiff_eq_w8Int]
      push_cast
      ring
    rw [hstep1, ← Finset.sum_div]
    congr 1
    exact Fintype.sum_bijective (fun d8 : Fin 8 → Bool => (⟨maskFromDiff8 d8, maskFromDiff8_lt d8⟩ : Fin 256))
      maskFromDiff8_bijective _ _ (fun _ => rfl)
  rw [hre]
  have hsum_eq : ∑ m : Fin 256, ((w8Int m.1 * cosLBInt m.1 : ℤ) : ℝ) =
      (sumPow2 8 0 (fun m => w8Int m * cosLBInt m) : ℝ) := by
    rw [sumPow2_eq_sum_Ico]
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun m => ((w8Int m * cosLBInt m : ℤ) : ℝ))]
    have hico : Finset.Ico 0 (0 + 2 ^ 8) = Finset.range 256 := by
      ext m; simp only [Finset.mem_Ico, Finset.mem_range]; omega
    rw [hico]
  rw [hsum_eq, le_div_iff₀ (by positivity : (0 : ℝ) < (200 : ℝ) ^ 8 * 1000000)]
  have hint : ((7442 : ℤ) * (200 ^ 8 : ℕ) * 100 : ℝ) ≤ (sumPow2 8 0 (fun m => w8Int m * cosLBInt m) : ℝ) := by
    exact_mod_cast check_total_int
  push_cast at hint
  linarith

private lemma sum_pDiff_marginal {n : ℕ} {k : ℕ} (hk : k + 8 ≤ n)
    (f : (Fin 8 → Bool) → ℝ) :
    ∑ d : Fin n → Bool, pDiff d * f (fun j : Fin 8 => d ⟨k + j.1, by omega⟩) =
      ∑ d8 : Fin 8 → Bool, pDiff d8 * f d8 := by
  let P : Fin n → Prop := fun i => k ≤ i.1 ∧ i.1 < k + 8
  let e := Equiv.piEquivPiSubtypeProd P (fun _ : Fin n => Bool)
  rw [← Fintype.sum_equiv e _ (fun x => pDiff (e.symm x) * f (fun j : Fin 8 => (e.symm x) ⟨k + j.1, by omega⟩))
    (fun d => by simp)]
  rw [Fintype.sum_prod_type]
  have hsplit : ∀ (d1 : {i : Fin n // P i} → Bool) (d2 : {i : Fin n // ¬ P i} → Bool),
      pDiff (e.symm (d1, d2)) = (∏ i : {i : Fin n // P i}, wBool (d1 i)) *
        (∏ i : {i : Fin n // ¬ P i}, wBool (d2 i)) := by
    intro d1 d2
    unfold pDiff
    rw [← Fintype.prod_subtype_mul_prod_subtype P (fun i => wBool (e.symm (d1, d2) i))]
    congr 1
    · apply Finset.prod_congr rfl; intro i _; simp [e]
    · apply Finset.prod_congr rfl; intro i _; simp [e]
  have hf_eq : ∀ (d1 : {i : Fin n // P i} → Bool) (d2 : {i : Fin n // ¬ P i} → Bool),
      (fun j : Fin 8 => (e.symm (d1, d2)) ⟨k + j.1, by omega⟩) =
        fun j : Fin 8 => d1 ⟨⟨k + j.1, by omega⟩, ⟨by omega, by omega⟩⟩ := by
    intro d1 d2; ext j; simp [e]
  simp_rw [hsplit, hf_eq]
  have hinner : ∀ d1 : {i : Fin n // P i} → Bool,
      ∑ d2 : {i : Fin n // ¬ P i} → Bool,
        (∏ i : {i : Fin n // P i}, wBool (d1 i)) * (∏ i : {i : Fin n // ¬ P i}, wBool (d2 i)) *
          f (fun j : Fin 8 => d1 ⟨⟨k + j.1, by omega⟩, ⟨by omega, by omega⟩⟩) =
      (∏ i : {i : Fin n // P i}, wBool (d1 i)) *
        f (fun j : Fin 8 => d1 ⟨⟨k + j.1, by omega⟩, ⟨by omega, by omega⟩⟩) := by
    intro d1
    have h1 : ∀ d2 : {i : Fin n // ¬ P i} → Bool,
        (∏ i : {i : Fin n // P i}, wBool (d1 i)) * (∏ i : {i : Fin n // ¬ P i}, wBool (d2 i)) *
          f (fun j : Fin 8 => d1 ⟨⟨k + j.1, by omega⟩, ⟨by omega, by omega⟩⟩) =
        ((∏ i : {i : Fin n // P i}, wBool (d1 i)) *
          f (fun j : Fin 8 => d1 ⟨⟨k + j.1, by omega⟩, ⟨by omega, by omega⟩⟩)) *
          (∏ i : {i : Fin n // ¬ P i}, wBool (d2 i)) := by intro d2; ring
    simp_rw [h1, ← Finset.mul_sum, ← Fintype.prod_sum]
    simp [sum_wBool]
  simp_rw [hinner]
  let idxEquiv : Fin 8 ≃ {i : Fin n // P i} := {
    toFun := fun j => ⟨⟨k + j.1, by omega⟩, ⟨by omega, by omega⟩⟩
    invFun := fun i => ⟨i.1.1 - k, by have := i.2; dsimp [P] at this; omega⟩
    left_inv := fun j => Fin.ext (by simp)
    right_inv := fun i => Subtype.ext (Fin.ext (by have := i.2; dsimp [P] at this; simp; omega))
  }
  let piEquiv : ({i : Fin n // P i} → Bool) ≃ (Fin 8 → Bool) :=
    Equiv.piCongrLeft' (fun _ => Bool) idxEquiv.symm
  refine Fintype.sum_equiv piEquiv _ (fun d8 => pDiff d8 * f d8) ?_
  intro d1
  congr 1
  · unfold pDiff
    symm
    exact Fintype.prod_equiv idxEquiv (fun j => wBool (piEquiv d1 j)) (fun i => wBool (d1 i))
      (fun j => by simp [piEquiv, Equiv.piCongrLeft'])
  · congr 1; ext j; simp [piEquiv, Equiv.piCongrLeft', idxEquiv]

private lemma expected_re_ge {n : ℕ} (hn : 9 ≤ n) :
    ((n + 1 - 9 : ℕ) : ℝ) * (7442 / 10000 : ℝ) - 9 ≤
      ∑ x : Bool × (Fin n → Bool), pState x *
        (∑ k ∈ Finset.range (n + 1),
          Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re := by
  have hre_sum : ∀ x : Bool × (Fin n → Bool),
      (∑ k ∈ Finset.range (n + 1),
        Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re =
      ∑ k ∈ Finset.range (n + 1),
        (Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re := by
    intro x; simp [Complex.re_sum]
  simp_rw [hre_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsplit : Finset.range (n + 1) = Finset.range (n + 1 - 9) ∪ Finset.Ico (n + 1 - 9) (n + 1) := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range (n + 1 - 9)) (Finset.Ico (n + 1 - 9) (n + 1)) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_range] at h1; simp only [Finset.mem_Ico] at h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hmain : ((n + 1 - 9 : ℕ) : ℝ) * (7442 / 10000 : ℝ) ≤
      ∑ k ∈ Finset.range (n + 1 - 9), ∑ x : Bool × (Fin n → Bool), pState x *
        (Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re := by
    calc ((n + 1 - 9 : ℕ) : ℝ) * (7442 / 10000 : ℝ)
        = ∑ _k ∈ Finset.range (n + 1 - 9), (7442 / 10000 : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
            apply Finset.sum_le_sum
            intro k hk
            have hk9 : k + 9 ≤ n + 1 := by
              have := Finset.mem_range.mp hk; omega
            have hk8 : k + 8 ≤ n := by omega
            have h1 : ∑ x : Bool × (Fin n → Bool), pState x *
                ((cosLBInt (maskFromDiff8 (fun j : Fin 8 => x.2 ⟨k + j.1, by omega⟩)) : ℝ) / 1000000) ≤
                ∑ x : Bool × (Fin n → Bool), pState x *
                  (Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re := by
              apply Finset.sum_le_sum
              intro x _
              apply mul_le_mul_of_nonneg_left _ (pState_nonneg x)
              have hterm := term_re_ge_cosLB x.1 x.2 hk9
              rwa [window9_reduced_eq x.1 x.2 hk9] at hterm
            refine le_trans ?_ h1
            unfold pState
            rw [Fintype.sum_prod_type]
            have hbool : ∀ d : Fin n → Bool,
                ∑ _b : Bool, (1 / 2 : ℝ) * pDiff d *
                  ((cosLBInt (maskFromDiff8 (fun j : Fin 8 => d ⟨k + j.1, by omega⟩)) : ℝ) / 1000000) =
                pDiff d * ((cosLBInt (maskFromDiff8 (fun j : Fin 8 => d ⟨k + j.1, by omega⟩)) : ℝ) / 1000000) := by
              intro d; simp; ring
            rw [Finset.sum_comm]
            simp_rw [hbool]
            rw [sum_pDiff_marginal hk8 (fun d8 => (cosLBInt (maskFromDiff8 d8) : ℝ) / 1000000)]
            exact sum_pDiff_cosLB8
  have htail : (-9 : ℝ) ≤
      ∑ k ∈ Finset.Ico (n + 1 - 9) (n + 1), ∑ x : Bool × (Fin n → Bool), pState x *
        (Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re := by
    calc (-9 : ℝ) = ∑ _k ∈ Finset.Ico (n + 1 - 9) (n + 1), (-1 : ℝ) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
            have : n + 1 - (n + 1 - 9) = 9 := by omega
            rw [this]; norm_num
      _ ≤ _ := by
            apply Finset.sum_le_sum
            intro k _
            have h1 : ∑ x : Bool × (Fin n → Bool), pState x * (-1 : ℝ) ≤
                ∑ x : Bool × (Fin n → Bool), pState x *
                  (Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re := by
              apply Finset.sum_le_sum
              intro x _
              apply mul_le_mul_of_nonneg_left _ (pState_nonneg x)
              rw [Complex.exp_ofReal_mul_I_re]
              exact Real.neg_one_le_cos _
            refine le_trans ?_ h1
            rw [← Finset.sum_mul, sum_pState]
            ring_nf; rfl
  linarith

-- Variance of number of flips under pDiff
private def flipCount {n : ℕ} (d : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => d i = true)).card

private lemma sum_pDiff_one_coord {n : ℕ} (i : Fin n) (g : Bool → ℝ) :
    ∑ d : Fin n → Bool, pDiff d * g (d i) = ∑ b : Bool, wBool b * g b := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : Fin n => j = i) (fun _ : Fin n => Bool)
  rw [← Fintype.sum_equiv e _ (fun x => pDiff (e.symm x) * g ((e.symm x) i)) (fun d => by simp)]
  rw [Fintype.sum_prod_type]
  have hsplit : ∀ (d1 : {j : Fin n // j = i} → Bool) (d2 : {j : Fin n // j ≠ i} → Bool),
      pDiff (e.symm (d1, d2)) * g ((e.symm (d1, d2)) i) =
      (wBool (d1 ⟨i, rfl⟩) * g (d1 ⟨i, rfl⟩)) * (∏ j : {j : Fin n // j ≠ i}, wBool (d2 j)) := by
    intro d1 d2
    unfold pDiff
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : Fin n => j = i) (fun j => wBool (e.symm (d1, d2) j))]
    have h1 : ∏ j : {j : Fin n // j = i}, wBool (e.symm (d1, d2) j) = wBool (d1 ⟨i, rfl⟩) := by
      have hunique : (Finset.univ : Finset {j : Fin n // j = i}) = {⟨i, rfl⟩} := by
        ext ⟨j, hj⟩; simp [hj]
      rw [hunique, Finset.prod_singleton]; simp [e]
    have h2 : ∏ j : {j : Fin n // j ≠ i}, wBool (e.symm (d1, d2) j) =
        ∏ j : {j : Fin n // j ≠ i}, wBool (d2 j) := by
      apply Finset.prod_congr rfl; intro j _; simp [e]
    have h3 : (e.symm (d1, d2)) i = d1 ⟨i, rfl⟩ := by simp [e]
    rw [h1, h2, h3]; ring
  simp_rw [hsplit, ← Finset.mul_sum, ← Fintype.prod_sum, sum_wBool, Finset.prod_const_one, mul_one]
  let e1 : ({j : Fin n // j = i} → Bool) ≃ Bool := {
    toFun := fun d1 => d1 ⟨i, rfl⟩
    invFun := fun b _ => b
    left_inv := fun d1 => by ext ⟨j, hj⟩; subst hj; rfl
    right_inv := fun _ => rfl
  }
  exact Fintype.sum_equiv e1 _ (fun b => wBool b * g b) (fun _ => rfl)

private lemma sum_pDiff_two_coords {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g1 g2 : Bool → ℝ) :
    ∑ d : Fin n → Bool, pDiff d * (g1 (d i) * g2 (d j)) =
      (∑ b : Bool, wBool b * g1 b) * (∑ b : Bool, wBool b * g2 b) := by
  let P : Fin n → Prop := fun r => r = i ∨ r = j
  let e := Equiv.piEquivPiSubtypeProd P (fun _ : Fin n => Bool)
  rw [← Fintype.sum_equiv e _ (fun x => pDiff (e.symm x) * (g1 ((e.symm x) i) * g2 ((e.symm x) j)))
    (fun d => by simp)]
  rw [Fintype.sum_prod_type]
  have hsplit : ∀ (d1 : {r : Fin n // P r} → Bool) (d2 : {r : Fin n // ¬ P r} → Bool),
      pDiff (e.symm (d1, d2)) * (g1 ((e.symm (d1, d2)) i) * g2 ((e.symm (d1, d2)) j)) =
      ((wBool (d1 ⟨i, Or.inl rfl⟩) * g1 (d1 ⟨i, Or.inl rfl⟩)) *
       (wBool (d1 ⟨j, Or.inr rfl⟩) * g2 (d1 ⟨j, Or.inr rfl⟩))) *
      (∏ r : {r : Fin n // ¬ P r}, wBool (d2 r)) := by
    intro d1 d2
    unfold pDiff
    rw [← Fintype.prod_subtype_mul_prod_subtype P (fun r => wBool (e.symm (d1, d2) r))]
    have hpair : (Finset.univ : Finset {r : Fin n // P r}) = {⟨i, Or.inl rfl⟩, ⟨j, Or.inr rfl⟩} := by
      ext ⟨r, hr⟩; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
      exact hr
    have hne : (⟨i, Or.inl rfl⟩ : {r : Fin n // P r}) ≠ ⟨j, Or.inr rfl⟩ := by
      intro h; exact hij (congrArg Subtype.val h)
    have h1 : ∏ r : {r : Fin n // P r}, wBool (e.symm (d1, d2) r) =
        wBool (d1 ⟨i, Or.inl rfl⟩) * wBool (d1 ⟨j, Or.inr rfl⟩) := by
      rw [hpair, Finset.prod_pair hne]; simp [e]
    have h2 : ∏ r : {r : Fin n // ¬ P r}, wBool (e.symm (d1, d2) r) =
        ∏ r : {r : Fin n // ¬ P r}, wBool (d2 r) := by
      apply Finset.prod_congr rfl; intro r _; simp [e]
    have h3 : (e.symm (d1, d2)) i = d1 ⟨i, Or.inl rfl⟩ := by simp [e]
    have h4 : (e.symm (d1, d2)) j = d1 ⟨j, Or.inr rfl⟩ := by simp [e]
    rw [h1, h2, h3, h4]; ring
  simp_rw [hsplit, ← Finset.mul_sum, ← Fintype.prod_sum, sum_wBool, Finset.prod_const_one, mul_one]
  let e2 : ({r : Fin n // P r} → Bool) ≃ Bool × Bool := {
    toFun := fun d1 => (d1 ⟨i, Or.inl rfl⟩, d1 ⟨j, Or.inr rfl⟩)
    invFun := fun p r => if r.1 = i then p.1 else p.2
    left_inv := fun d1 => by
      ext ⟨r, hr⟩
      rcases hr with rfl | rfl
      · simp
      · simp [hij.symm]
    right_inv := fun ⟨b1, b2⟩ => by simp [hij.symm]
  }
  rw [Fintype.sum_equiv e2 _ (fun p => (wBool p.1 * g1 p.1) * (wBool p.2 * g2 p.2)) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp [← Finset.mul_sum, ← Finset.sum_mul]

private lemma variance_flipCount (n : ℕ) :
    ∑ d : Fin n → Bool, pDiff d * ((flipCount d : ℝ) - (n : ℝ) * qR) ^ 2 =
      (n : ℝ) * qR * (1 - qR) := by
  let g (b : Bool) : ℝ := (if b = true then 1 else 0) - qR
  have hg_mean : ∑ b : Bool, wBool b * g b = 0 := by
    simp [wBool, g, qR]; ring
  have hg_sq : ∑ b : Bool, wBool b * (g b * g b) = qR * (1 - qR) := by
    simp [wBool, g, qR]; ring
  have hdev : ∀ d : Fin n → Bool, (flipCount d : ℝ) - (n : ℝ) * qR = ∑ i : Fin n, g (d i) := by
    intro d
    unfold flipCount
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_boole]
  have hsq : ∀ d : Fin n → Bool,
      pDiff d * ((flipCount d : ℝ) - (n : ℝ) * qR) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, pDiff d * (g (d i) * g (d j)) := by
    intro d
    rw [hdev d, sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hinner : ∀ i : Fin n,
      ∑ d : Fin n → Bool, ∑ j : Fin n, pDiff d * (g (d i) * g (d j)) = qR * (1 - qR) := by
    intro i
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i]
    · rw [sum_pDiff_one_coord i (fun b => g b * g b), hg_sq]
    · intro j _ hji
      rw [sum_pDiff_two_coords hji.symm g g, hg_mean, mul_zero]
    · intro hi; exfalso; exact hi (Finset.mem_univ i)
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma pDiff_pow_2500_le {n : ℕ} {d : Fin n → Bool}
    (hge : 53 * (n + 1) ≤ 625 * flipCount d) :
    (pDiff d) ^ 2500 ≤ ((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500 := by
  set r := flipCount d
  have hr_le : r ≤ n := by
    calc r ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := by simp
  have hp_eq : pDiff d = (17 / 200 : ℝ) ^ r * (183 / 200 : ℝ) ^ (n - r) := by
    unfold pDiff wBool qR
    have h1 : ∀ j : Fin n, (if d j = true then (17 / 200 : ℝ) else 1 - 17 / 200) =
        if d j = true then (17 / 200 : ℝ) else (183 / 200 : ℝ) := by
      intro j; split_ifs <;> norm_num
    simp_rw [h1]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hcomp : (Finset.univ.filter (fun j : Fin n => ¬ d j = true)).card = n - r := by
      have htot := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin n)))
        (p := fun j => d j = true)
      simp only [Finset.card_univ, Fintype.card_fin] at htot
      omega
    rw [hcomp]
  rw [hp_eq, mul_pow, ← pow_mul, ← pow_mul]
  have h212 : 212 * (n + 1) ≤ r * 2500 := by omega
  have hdiff_eq : (n - r) * 2500 + 2500 = 2500 * (n + 1) - r * 2500 := by omega
  have hmul : (17 / 200 : ℝ) ^ (r * 2500) * (183 / 200 : ℝ) ^ ((n - r) * 2500) =
      ((17 / 200 : ℝ) ^ (r * 2500) * (183 / 200 : ℝ) ^ (2500 * (n + 1) - r * 2500)) *
        (200 / 183 : ℝ) ^ 2500 := by
    have h183 : (183 / 200 : ℝ) ^ 2500 * (200 / 183 : ℝ) ^ 2500 = 1 := by
      rw [← mul_pow]; norm_num
    rw [mul_assoc, ← pow_add, hdiff_eq]
    calc (17 / 200 : ℝ) ^ (r * 2500) * (183 / 200 : ℝ) ^ ((n - r) * 2500)
        = (17 / 200 : ℝ) ^ (r * 2500) * ((183 / 200 : ℝ) ^ ((n - r) * 2500) *
            ((183 / 200 : ℝ) ^ 2500 * (200 / 183 : ℝ) ^ 2500)) := by rw [h183, mul_one]
      _ = (17 / 200 : ℝ) ^ (r * 2500) * ((183 / 200 : ℝ) ^ ((n - r) * 2500 + 2500) *
            (200 / 183 : ℝ) ^ 2500) := by rw [pow_add, mul_assoc]
      _ = (17 / 200 : ℝ) ^ (r * 2500) * ((183 / 200 : ℝ) ^ (2500 * (n + 1) - r * 2500) *
            (200 / 183 : ℝ) ^ 2500) := by rw [hdiff_eq]
      _ = _ := by ring
  rw [hmul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  set delta := r * 2500 - 212 * (n + 1)
  have hr_split : r * 2500 = 212 * (n + 1) + delta := by omega
  have hrem_split : 2288 * (n + 1) = (2500 * (n + 1) - r * 2500) + delta := by omega
  have hmono : (17 / 200 : ℝ) ^ (r * 2500) * (183 / 200 : ℝ) ^ (2500 * (n + 1) - r * 2500) ≤
      (17 / 200 : ℝ) ^ (212 * (n + 1)) * (183 / 200 : ℝ) ^ (2288 * (n + 1)) := by
    rw [hr_split, hrem_split, pow_add, pow_add]
    have hle_delta : (17 / 200 : ℝ) ^ delta ≤ (183 / 200 : ℝ) ^ delta :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) delta
    have h1 : (17 / 200 : ℝ) ^ (212 * (n + 1)) * (17 / 200 : ℝ) ^ delta *
        (183 / 200 : ℝ) ^ (2500 * (n + 1) - r * 2500) =
        ((17 / 200 : ℝ) ^ (212 * (n + 1)) * (183 / 200 : ℝ) ^ (2500 * (n + 1) - r * 2500)) *
          (17 / 200 : ℝ) ^ delta := by ring
    have h2 : (17 / 200 : ℝ) ^ (212 * (n + 1)) *
        ((183 / 200 : ℝ) ^ (2500 * (n + 1) - r * 2500) * (183 / 200 : ℝ) ^ delta) =
        ((17 / 200 : ℝ) ^ (212 * (n + 1)) * (183 / 200 : ℝ) ^ (2500 * (n + 1) - r * 2500)) *
          (183 / 200 : ℝ) ^ delta := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hle_delta (by positivity)
  refine hmono.trans ?_
  rw [pow_mul, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) check_ent_real (n + 1)

theorem main_theorem :
    (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∃ (x2 : ℕ), ∀ x3 ≥ x2, ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x3), (2 : ℝ) ^ (-((291 / 500 : ℝ) * ↑x3)) ≤ ↑x5.card / (2 : ℝ) ^ x3 ∧ ∀ x6 ∈ x5, (93 / 125 : ℝ) * ↑x3 + (2 : ℝ) * Real.pi / (65536 : ℝ) * ↑x3 + (2 : ℝ) * Real.pi < ‖x1 x3 (↑x6 / (2 : ℝ) ^ x3)‖) := by
  dsimp only
  refine ⟨200000000, ?_⟩
  intro L hL
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hn : 199999999 ≤ n := by omega
  let S (x : Bool × (Fin n → Bool)) : ℂ :=
    ∑ k ∈ Finset.range (n + 1),
      Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)
  let thresh : ℝ := (93 / 125 : ℝ) * ((n + 1 : ℕ) : ℝ) + (2 : ℝ) * Real.pi / (65536 : ℝ) * ((n + 1 : ℕ) : ℝ) + (2 : ℝ) * Real.pi
  let Bad : Finset (Bool × (Fin n → Bool)) :=
    Finset.univ.filter (fun x => 625 * flipCount x.2 < 53 * (n + 1))
  let Good : Finset (Bool × (Fin n → Bool)) :=
    Finset.univ.filter (fun x => 53 * (n + 1) ≤ 625 * flipCount x.2 ∧ thresh < (S x).re)
  -- Step 1: P(Bad) ≤ 1 / 100000
  have hBad : ∑ x ∈ Bad, pState x ≤ 1 / 100000 := by
    have hdev_lb : ∀ x ∈ Bad, ((n + 1 : ℕ) : ℝ) / 10000 ≤ (n : ℝ) * qR - (flipCount x.2 : ℝ) := by
      intro x hx
      have hlt : 625 * flipCount x.2 < 53 * (n + 1) := (Finset.mem_filter.mp hx).2
      have hlt_r : 625 * (flipCount x.2 : ℝ) ≤ 53 * ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hlt.le
      have hn_r : (199999999 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      dsimp [qR]
      push_cast at hlt_r ⊢
      linarith
    have hmarkov : (((n + 1 : ℕ) : ℝ) / 10000) ^ 2 * ∑ x ∈ Bad, pState x ≤ (n : ℝ) * qR * (1 - qR) := by
      calc (((n + 1 : ℕ) : ℝ) / 10000) ^ 2 * ∑ x ∈ Bad, pState x
          = ∑ x ∈ Bad, pState x * (((n + 1 : ℕ) : ℝ) / 10000) ^ 2 := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
        _ ≤ ∑ x ∈ Bad, pState x * ((flipCount x.2 : ℝ) - (n : ℝ) * qR) ^ 2 := by
              apply Finset.sum_le_sum
              intro x hx
              apply mul_le_mul_of_nonneg_left _ (pState_nonneg x)
              have h1 := hdev_lb x hx
              have h0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / 10000 := by positivity
              nlinarith
        _ ≤ ∑ x : Bool × (Fin n → Bool), pState x * ((flipCount x.2 : ℝ) - (n : ℝ) * qR) ^ 2 := by
              apply Finset.sum_le_univ_sum_of_nonneg
              intro x; exact mul_nonneg (pState_nonneg x) (sq_nonneg _)
        _ = (n : ℝ) * qR * (1 - qR) := by
              unfold pState
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              have hb : ∀ d : Fin n → Bool,
                  ∑ _b : Bool, (1 / 2 : ℝ) * pDiff d * ((flipCount d : ℝ) - (n : ℝ) * qR) ^ 2 =
                  pDiff d * ((flipCount d : ℝ) - (n : ℝ) * qR) ^ 2 := by
                intro d; simp; ring
              simp_rw [hb]
              exact variance_flipCount n
    have hn_r : (199999999 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) / 10000) ^ 2 := by positivity
    dsimp [qR] at hmarkov
    push_cast at hmarkov ⊢
    nlinarith
  -- Step 2: P(Good) ≥ 1 / 100000
  have hS_ub : ∀ x : Bool × (Fin n → Bool), (S x).re ≤ ((n + 1 : ℕ) : ℝ) := by
    intro x
    dsimp [S]
    rw [Complex.re_sum]
    calc ∑ k ∈ Finset.range (n + 1),
          (Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * ((toNatBits x.1 x.2 : ℝ) / (2 : ℝ) ^ (n + 1))⌋ / (65536 : ℝ)) * Complex.I)).re
        ≤ ∑ _k ∈ Finset.range (n + 1), (1 : ℝ) := by
            apply Finset.sum_le_sum; intro k _
            rw [Complex.exp_ofReal_mul_I_re]
            exact Real.cos_le_one _
      _ = ((n + 1 : ℕ) : ℝ) := by simp
  have hGood_prob : (1 / 100000 : ℝ) ≤ ∑ x ∈ Good, pState x := by
    have hexp := expected_re_ge (show 9 ≤ n by omega)
    have hupper : ∑ x : Bool × (Fin n → Bool), pState x * (S x).re ≤
        ((n + 1 : ℕ) : ℝ) * (∑ x ∈ Good, pState x) +
        ((n + 1 : ℕ) : ℝ) * (∑ x ∈ Bad, pState x) + thresh := by
      have hpw : ∀ x : Bool × (Fin n → Bool),
          pState x * (S x).re ≤
            (if x ∈ Good then pState x * ((n + 1 : ℕ) : ℝ) else 0) +
            (if x ∈ Bad then pState x * ((n + 1 : ℕ) : ℝ) else 0) +
            pState x * thresh := by
        intro x
        have hpx := pState_nonneg x
        have hth : 0 ≤ thresh := by
          dsimp [thresh]; positivity
        by_cases hG : x ∈ Good
        · simp only [hG, ↓reduceIte]
          have h1 : pState x * (S x).re ≤ pState x * ((n + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (hS_ub x) hpx
          have h2 : 0 ≤ if x ∈ Bad then pState x * ((n + 1 : ℕ) : ℝ) else 0 := by
            split_ifs <;> positivity
          have h3 : 0 ≤ pState x * thresh := mul_nonneg hpx hth
          linarith
        · by_cases hB : x ∈ Bad
          · simp only [hG, hB, ↓reduceIte, zero_add]
            have h1 : pState x * (S x).re ≤ pState x * ((n + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (hS_ub x) hpx
            have h3 : 0 ≤ pState x * thresh := mul_nonneg hpx hth
            linarith
          · simp only [hG, hB, ↓reduceIte, zero_add]
            have hle_th : (S x).re ≤ thresh := by
              by_contra hgt
              push_neg at hgt
              have hnotBad : 53 * (n + 1) ≤ 625 * flipCount x.2 := by
                have := mt (Finset.mem_filter.mpr)
                have hnb : ¬ (625 * flipCount x.2 < 53 * (n + 1)) := fun hc =>
                  hB (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hc⟩)
                omega
              exact hG (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hnotBad, hgt⟩)
            exact mul_le_mul_of_nonneg_left hle_th hpx
      calc ∑ x : Bool × (Fin n → Bool), pState x * (S x).re
          ≤ ∑ x : Bool × (Fin n → Bool),
              ((if x ∈ Good then pState x * ((n + 1 : ℕ) : ℝ) else 0) +
               (if x ∈ Bad then pState x * ((n + 1 : ℕ) : ℝ) else 0) +
               pState x * thresh) := Finset.sum_le_sum (fun x _ => hpw x)
        _ = (∑ x ∈ Good, pState x * ((n + 1 : ℕ) : ℝ)) +
            (∑ x ∈ Bad, pState x * ((n + 1 : ℕ) : ℝ)) +
            (∑ x : Bool × (Fin n → Bool), pState x * thresh) := by
              simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
        _ = ((n + 1 : ℕ) : ℝ) * (∑ x ∈ Good, pState x) +
            ((n + 1 : ℕ) : ℝ) * (∑ x ∈ Bad, pState x) + thresh := by
              rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, sum_pState, one_mul]
              ring
    have hpi_hi : Real.pi < (31416 / 10000 : ℝ) := by linarith [Real.pi_lt_d4]
    have hn_r : (199999999 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsub_r : ((n + 1 - 9 : ℕ) : ℝ) = (n : ℝ) - 8 := by
      have : (n + 1 - 9 : ℕ) + 9 = n + 1 := by omega
      have hcast : ((n + 1 - 9 : ℕ) : ℝ) + 9 = (n : ℝ) + 1 := by exact_mod_cast this
      linarith
    have hth_ub : thresh ≤ (7441 / 10000 : ℝ) * ((n : ℝ) + 1) + 7 := by
      dsimp [thresh]
      push_cast
      nlinarith
    have hcomb : ((n : ℝ) - 8) * (7442 / 10000 : ℝ) - 9 ≤
        ((n : ℝ) + 1) * (∑ x ∈ Good, pState x) + ((n : ℝ) + 1) * (1 / 100000 : ℝ) +
          ((7441 / 10000 : ℝ) * ((n : ℝ) + 1) + 7) := by
      rw [← hsub_r]
      have h1 : ((n + 1 - 9 : ℕ) : ℝ) * (7442 / 10000 : ℝ) - 9 ≤
          ((n + 1 : ℕ) : ℝ) * (∑ x ∈ Good, pState x) +
          ((n + 1 : ℕ) : ℝ) * (∑ x ∈ Bad, pState x) + thresh := hexp.trans hupper
      have h2 : ((n + 1 : ℕ) : ℝ) * (∑ x ∈ Bad, pState x) ≤ ((n + 1 : ℕ) : ℝ) * (1 / 100000 : ℝ) :=
        mul_le_mul_of_nonneg_left hBad (by positivity)
      push_cast at h1 h2
      linarith
    nlinarith
  -- Step 3: Lower bound on Good.card using 2500-th power
  have hGood_card : (2 : ℝ) ^ ((209 / 500 : ℝ) * ((n + 1 : ℕ) : ℝ)) ≤ (Good.card : ℝ) := by
    have hsum_le : ∑ x ∈ Good, pState x ≤
        (Good.card : ℝ) * (((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500) ^ ((1 : ℝ) / 2500) := by
      calc ∑ x ∈ Good, pState x
          ≤ ∑ _x ∈ Good, (((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500) ^ ((1 : ℝ) / 2500) := by
              apply Finset.sum_le_sum
              intro x hx
              have hge : 53 * (n + 1) ≤ 625 * flipCount x.2 := (Finset.mem_filter.mp hx).2.1
              have hp2500 : (pState x) ^ 2500 ≤ ((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500 := by
                have h1 : pState x ≤ pDiff x.2 := by
                  unfold pState; linarith [pDiff_nonneg x.2]
                exact (pow_le_pow_left₀ (pState_nonneg x) h1 2500).trans (pDiff_pow_2500_le hge)
              have hpow_eq : ((((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500) ^ ((1 : ℝ) / 2500)) ^ (2500 : ℕ) =
                  ((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500 := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
                norm_num
              exact le_of_pow_le_pow_left₀ (by norm_num : (2500 : ℕ) ≠ 0) (by positivity) (by rw [hpow_eq]; exact hp2500)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hpow2500 : (1 / 100000 : ℝ) ^ 2500 ≤
        (Good.card : ℝ) ^ 2500 * (((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500) := by
      have h1 := pow_le_pow_left₀ (by positivity) (hGood_prob.trans hsum_le) 2500
      rw [mul_pow] at h1
      have hpow_eq : ((((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500) ^ ((1 : ℝ) / 2500)) ^ (2500 : ℕ) =
          ((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rwa [hpow_eq] at h1
    have hcard_pow : (2 : ℝ) ^ (1045 * (n + 1)) ≤ (Good.card : ℝ) ^ 2500 := by
      have h2_1046_pos : (0 : ℝ) < ((2 : ℝ) ^ 1046) ^ (n + 1) := by positivity
      have hmul : (1 / 100000 : ℝ) ^ 2500 * ((2 : ℝ) ^ 1046) ^ (n + 1) ≤
          (Good.card : ℝ) ^ 2500 * (200 / 183 : ℝ) ^ 2500 := by
        have h := mul_le_mul_of_nonneg_right hpow2500 h2_1046_pos.le
        have hinv : (((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1)) * ((2 : ℝ) ^ 1046) ^ (n + 1) = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
        calc (1 / 100000 : ℝ) ^ 2500 * ((2 : ℝ) ^ 1046) ^ (n + 1)
            ≤ (Good.card : ℝ) ^ 2500 * (((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1) * (200 / 183 : ℝ) ^ 2500) *
                ((2 : ℝ) ^ 1046) ^ (n + 1) := h
          _ = (Good.card : ℝ) ^ 2500 * (200 / 183 : ℝ) ^ 2500 *
                ((((2 : ℝ) ^ 1046)⁻¹ ^ (n + 1)) * ((2 : ℝ) ^ 1046) ^ (n + 1)) := by ring
          _ = (Good.card : ℝ) ^ 2500 * (200 / 183 : ℝ) ^ 2500 := by rw [hinv, mul_one]
      have hconst : (200 / 183 : ℝ) ^ 2500 * (100000 : ℝ) ^ 2500 ≤ (2 : ℝ) ^ (n + 1) := by
        have h1 : (200 / 183 : ℝ) * 100000 ≤ (2 : ℝ) ^ 18 := by norm_num
        have h2 : ((200 / 183 : ℝ) * 100000) ^ 2500 ≤ ((2 : ℝ) ^ 18) ^ 2500 :=
          pow_le_pow_left₀ (by positivity) h1 2500
        rw [mul_pow, ← pow_mul] at h2
        refine h2.trans ?_
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hsplit2 : ((2 : ℝ) ^ 1046) ^ (n + 1) = (2 : ℝ) ^ (1045 * (n + 1)) * (2 : ℝ) ^ (n + 1) := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [hsplit2] at hmul
      have hstep : (2 : ℝ) ^ (1045 * (n + 1)) * (200 / 183 : ℝ) ^ 2500 ≤
          (1 / 100000 : ℝ) ^ 2500 * ((2 : ℝ) ^ (1045 * (n + 1)) * (2 : ℝ) ^ (n + 1)) := by
        have h1 : (200 / 183 : ℝ) ^ 2500 ≤ (1 / 100000 : ℝ) ^ 2500 * (2 : ℝ) ^ (n + 1) := by
          have hinv : (1 / 100000 : ℝ) ^ 2500 * (100000 : ℝ) ^ 2500 = 1 := by
            rw [← mul_pow]; norm_num
          calc (200 / 183 : ℝ) ^ 2500
              = (1 / 100000 : ℝ) ^ 2500 * ((200 / 183 : ℝ) ^ 2500 * (100000 : ℝ) ^ 2500) := by
                  rw [← mul_assoc, mul_comm ((1 / 100000 : ℝ) ^ 2500), mul_assoc, hinv, mul_one]
            _ ≤ (1 / 100000 : ℝ) ^ 2500 * (2 : ℝ) ^ (n + 1) :=
                  mul_le_mul_of_nonneg_left hconst (by positivity)
        calc (2 : ℝ) ^ (1045 * (n + 1)) * (200 / 183 : ℝ) ^ 2500
            ≤ (2 : ℝ) ^ (1045 * (n + 1)) * ((1 / 100000 : ℝ) ^ 2500 * (2 : ℝ) ^ (n + 1)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by ring
      exact le_of_mul_le_mul_right (hstep.trans hmul) (by positivity : (0 : ℝ) < (200 / 183 : ℝ) ^ 2500)
    have hrpow_eq : ((2 : ℝ) ^ ((209 / 500 : ℝ) * ((n + 1 : ℕ) : ℝ))) ^ (2500 : ℕ) =
        (2 : ℝ) ^ (1045 * (n + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      have hexp : (209 / 500 : ℝ) * ((n + 1 : ℕ) : ℝ) * (2500 : ℕ) = ((1045 * (n + 1) : ℕ) : ℝ) := by
        push_cast; ring
      rw [hexp, Real.rpow_natCast]
    exact le_of_pow_le_pow_left₀ (by norm_num : (2500 : ℕ) ≠ 0) (by positivity) (by rw [hrpow_eq]; exact hcard_pow)
  -- Step 4: Map Good into Finset.range (2 ^ (n + 1))
  let x5 : Finset ℕ := Good.image (fun x => toNatBits x.1 x.2)
  refine ⟨x5, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨x, _, rfl⟩
    exact Finset.mem_range.mpr (toNatBits_lt x.1 x.2)
  · have hcard_eq : x5.card = Good.card :=
      Finset.card_image_of_injective Good toNatBits_injective
    rw [hcard_eq, le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n + 1))]
    rw [← Real.rpow_natCast (2 : ℝ) (n + 1), ← Real.rpow_add (by positivity : (0 : ℝ) < 2)]
    have hexp : -((291 / 500 : ℝ) * ((n + 1 : ℕ) : ℝ)) + ((n + 1 : ℕ) : ℝ) =
        (209 / 500 : ℝ) * ((n + 1 : ℕ) : ℝ) := by ring
    rw [hexp]
    exact hGood_card
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨x, hx, rfl⟩
    have hlt : thresh < (S x).re := (Finset.mem_filter.mp hx).2.2
    exact lt_of_lt_of_le hlt (Complex.re_le_norm (S x))

end Conjectures.Cuts.Task505efd43Proof

theorem Conjectures.Cuts.Task505efd43f116fe6cd3165ce2 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∃ (x2 : ℕ), ∀ x3 ≥ x2, ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x3), (2 : ℝ) ^ (-((291 / 500 : ℝ) * ↑x3)) ≤ ↑x5.card / (2 : ℝ) ^ x3 ∧ ∀ x6 ∈ x5, (93 / 125 : ℝ) * ↑x3 + (2 : ℝ) * Real.pi / (65536 : ℝ) * ↑x3 + (2 : ℝ) * Real.pi < ‖x1 x3 (↑x6 / (2 : ℝ) ^ x3)‖) :=
  Conjectures.Cuts.Task505efd43Proof.main_theorem

