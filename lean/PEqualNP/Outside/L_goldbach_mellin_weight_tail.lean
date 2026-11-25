import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_mellin_weight_tail :
  let Z := fun (m k : ℕ) (γ : Fin m → ℝ) =>
    Finset.univ.filter (fun j => (k:ℝ) ≤ |γ j| ∧ |γ j| < (k+1:ℕ));
  ∀ a : ℕ, ∃ C : ℝ, 0<C ∧ ∀ (m d H : ℕ) (γ : Fin m → ℝ) (W : ℝ → ℂ) (K L : ℝ),
    1≤d → 0≤K → 0≤L → (∀ t, ‖W t‖ ≤ K/(1+|t|)^(a+4)) →
    (∀ k, ((Z m k γ).card:ℝ) ≤ L*Real.log ((d*(k+2):ℕ):ℝ)) →
    (∑ j ∈ Finset.univ.filter (fun i => (H:ℝ) ≤ |γ i|), ‖W (γ j)‖) ≤
      C*K*L*Real.log ((d*(H+2):ℕ):ℝ)/((H+1:ℕ):ℝ)^(a+2) := by
  classical
  dsimp only
  intro a
  refine ⟨4, by norm_num, ?_⟩
  intro m d H γ W K L hd hK hL hW hcount
  let u : ℕ → ℝ := fun k => k + 1
  let y : ℝ := (d * (H + 2) : ℕ)
  have hu k : 0 < u k := by dsimp [u]; positivity
  have hu_one k : 1 ≤ u k := le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hu_succ k : u (k + 1) = u k + 1 := by simp [u, add_assoc]
  have hy2 : 2 ≤ y := by
    have : 2 ≤ d * (H+2) := calc
      2 ≤ H + 2 := by omega
      _ = 1 * (H + 2) := by simp
      _ ≤ d * (H + 2) := Nat.mul_le_mul_right _ hd
    change (2:ℝ) ≤ ((d * (H+2) : ℕ) : ℝ)
    exact_mod_cast this
  have hy : 0 < y := by linarith only [hy2]
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy2])
  have hlog (k : ℕ) : Real.log ((d*(k+2):ℕ):ℝ) ≤ 2 * u k * Real.log y := by
    have hxNat : 0 < d * (k + 2) := Nat.mul_pos (by omega) (by omega)
    have hx : 0 < ((d*(k+2):ℕ):ℝ) := by exact_mod_cast hxNat
    have hbound : d * (k+2) ≤ (d * (H+2)) * 2^(k+1) := calc
      d * (k+2) ≤ d * 2^(k+1) :=
        Nat.mul_le_mul_left d (Nat.succ_le_of_lt (Nat.lt_pow_self (n := k+1) (by decide)))
      _ = (d * 1) * 2^(k+1) := by simp
      _ ≤ (d * (H+2)) * 2^(k+1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have hboundR : ((d*(k+2):ℕ):ℝ) ≤ y * (2:ℝ)^(k+1) := by
      change _ ≤ ((d*(H+2):ℕ):ℝ) * (2:ℝ)^(k+1)
      exact_mod_cast hbound
    have hlogtwo : Real.log 2 ≤ Real.log y :=
      Real.log_le_log (by norm_num) hy2
    calc
      _ ≤ Real.log (y * (2:ℝ)^(k+1)) := Real.log_le_log hx hboundR
      _ = Real.log y + u k * Real.log 2 := by
        rw [Real.log_mul hy.ne' (by positivity), Real.log_pow]
        simp [u]
      _ ≤ Real.log y + u k * Real.log y := by
        have hmul := mul_le_mul_of_nonneg_left hlogtwo (hu k).le
        linarith only [hmul]
      _ ≤ 2 * u k * Real.log y := by
        have h := mul_le_mul_of_nonneg_right (hu_one k) hlogy
        linarith only [h]
  let S : Finset (Fin m) := Finset.univ.filter (fun i => (H:ℝ) ≤ |γ i|)
  let bin : Fin m → ℕ := fun i => ⌊|γ i|⌋₊
  let N := max H ((Finset.univ : Finset (Fin m)).sup bin + 1)
  let F : ℕ → Finset (Fin m) := fun k => S.filter (fun i => bin i = k)
  have hmaps : ∀ i ∈ S, bin i ∈ Finset.Ico H N := by
    intro i hi
    apply Finset.mem_Ico.mpr
    refine ⟨Nat.le_floor (Finset.mem_filter.mp hi).2, ?_⟩
    have hs : bin i ≤ (Finset.univ : Finset (Fin m)).sup bin :=
      Finset.le_sup (Finset.mem_univ i)
    exact lt_of_lt_of_le (Nat.lt_succ_of_le hs) (le_max_right _ _)
  have hbin {i k} (hi : i ∈ F k) : (k:ℝ) ≤ |γ i| ∧ |γ i| < (k:ℝ) + 1 :=
    (Nat.floor_eq_iff (abs_nonneg (γ i))).mp (Finset.mem_filter.mp hi).2
  have hcountF (k : ℕ) : ((F k).card:ℝ) ≤ L * Real.log ((d*(k+2):ℕ):ℝ) := by
    refine le_trans ?_ (hcount k)
    exact_mod_cast Finset.card_le_card (show F k ⊆
      Finset.univ.filter (fun j => (k:ℝ) ≤ |γ j| ∧ |γ j| < (k+1:ℕ)) from
        fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
          simpa using hbin hi⟩)
  let D : ℝ := (2*K*L*Real.log y) / u H^(a+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hfiber (k : ℕ) (hk : k ∈ Finset.Ico H N) :
      (∑ i ∈ F k, ‖W (γ i)‖) ≤ D * (1 / u k^2) := by
    have hdom : u H ≤ u k := by
      dsimp [u]
      have hcast : (H:ℝ) ≤ (k:ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hk).1
      linarith only [hcast]
    have hpow : u H^(a+1)*u k^2 ≤ u k^(a+3) := calc
      _ ≤ u k^(a+1)*u k^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hu H).le hdom _) (sq_nonneg _)
      _ = _ := by rw [← pow_add]
    calc
      _ ≤ ∑ _i ∈ F k, K / u k^(a+4) := by
        refine Finset.sum_le_sum fun i hi => (hW (γ i)).trans ?_
        apply div_le_div_of_nonneg_left hK (pow_pos (hu k) _)
        exact pow_le_pow_left₀ (hu k).le (by simpa [u, add_comm] using (hbin hi).1) _
      _ = ((F k).card:ℝ) * (K / u k^(a+4)) := by simp [nsmul_eq_mul]
      _ ≤ (L * Real.log ((d*(k+2):ℕ):ℝ)) * (K / u k^(a+4)) :=
        mul_le_mul_of_nonneg_right (hcountF k) (by positivity)
      _ ≤ (L * (2 * u k * Real.log y)) * (K / u k^(a+4)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlog k) hL) (by positivity)
      _ = (2*K*L*Real.log y) / u k^(a+3) := by
        rw [show a+4=(a+3)+1 by omega, pow_succ]
        field_simp [ne_of_gt (hu k)]
        <;> ring
      _ ≤ (2*K*L*Real.log y) / (u H^(a+1)*u k^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = D * (1 / u k^2) := by
        dsimp [D]
        field_simp [ne_of_gt (hu H), ne_of_gt (hu k)]
  have hstep (k : ℕ) : 1/u k^2 ≤ 2*(1/u k - 1/u (k+1)) := by
    rw [hu_succ]
    have hu2 : 0 < u k + 1 := by positivity
    have he : 1/u k - 1/(u k+1) = 1/(u k*(u k+1)) := by
      field_simp [ne_of_gt (hu k), ne_of_gt hu2]
      <;> ring
    rw [he, ← mul_div_assoc, mul_one]
    apply (div_le_div_iff₀ (pow_pos (hu k) _) (mul_pos (hu k) hu2)).mpr
    nlinarith only [mul_nonneg (hu k).le (sub_nonneg.mpr (hu_one k))]
  have htelescope (M : ℕ) :
      (∑ k ∈ Finset.range M, (1/u k - 1/u (k+1))) = 1/u 0 - 1/u M := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; ring
  have hsum : (∑ k ∈ Finset.Ico H N, 1/u k^2) ≤ 2/u H := calc
    _ ≤ ∑ k ∈ Finset.Ico H N, 2*(1/u k - 1/u (k+1)) :=
      Finset.sum_le_sum (fun k _ => hstep k)
    _ = 2*(1/u H - 1/u N) := by
      rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ (show H ≤ N from le_max_left _ _),
        htelescope, htelescope]
      ring
    _ ≤ _ := by
      rw [show (2:ℝ)/u H = 2*(1/u H) by ring]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by norm_num)
  calc
    (∑ i ∈ S, ‖W (γ i)‖) = ∑ k ∈ Finset.Ico H N, ∑ i ∈ F k, ‖W (γ i)‖ :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.Ico H N, D * (1/u k^2) :=
      Finset.sum_le_sum hfiber
    _ = D * (∑ k ∈ Finset.Ico H N, 1/u k^2) := by rw [Finset.mul_sum]
    _ ≤ D * (2/u H) := mul_le_mul_of_nonneg_left hsum hD
    _ = _ := by
      rw [show ((H+1:ℕ):ℝ) = u H by simp [u]]
      change D * (2/u H) = 4*K*L*Real.log y / u H^(a+2)
      dsimp only [D]
      rw [show a+2=(a+1)+1 by omega, pow_succ]
      field_simp [ne_of_gt (hu H)]
      <;> ring
