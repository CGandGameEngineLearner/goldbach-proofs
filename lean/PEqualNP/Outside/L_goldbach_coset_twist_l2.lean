import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_twist_l2 :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q L : ℕ) (z : ℂ), 0<q → 2*(n/q)<L → IsPrimitiveRoot z L → (∑ j ∈ Finset.range L, ‖Y n q (z^j)-(B n n:ℂ)‖^2)/(L:ℝ) = ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q))^2+(B n (n-h*q))^2) := by
  intro w B Y n q L z hq h2HL hz
  let H : ℕ := n / q
  have hL : 0 < L := by omega
  have hz_pow : z ^ L = 1 := hz.pow_eq_one
  have hz_ne : z ≠ 0 := by
    intro h0
    have h := hz_pow
    rw [h0, zero_pow (by omega)] at h
    exact zero_ne_one h
  have hpow_lt : ∀ (x y : ℝ) (k : ℕ), 0 ≤ x → x < y → 0 < k → x ^ k < y ^ k := by
    intro x y k hx hxy hk
    induction k with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hxy
      | succ k =>
        have hlt := ih (by omega)
        have hy : 0 < y := by linarith
        have hxk : 0 ≤ x ^ (k + 1) := pow_nonneg hx _
        rw [pow_succ, pow_succ]
        nlinarith
  have hnorm : ‖z‖ = 1 := by
    have hpow_norm : ‖z‖ ^ L = 1 := by
      rw [← norm_pow, hz_pow, norm_one]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg z
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hpow_lt ‖z‖ 1 L hnn hlt hL
      rw [one_pow] at this
      linarith
    · have := hpow_lt 1 ‖z‖ L (by norm_num) hgt hL
      rw [one_pow] at this
      linarith
  have hconj : starRingEnd ℂ z = z⁻¹ := by
    have h1 : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj', hnorm]
      norm_num
    have h2 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz_ne
    exact mul_left_cancel₀ hz_ne (h1.trans h2.symm)
  have hinvL : (z⁻¹) ^ L = 1 := by
    rw [← hconj, ← map_pow, hz_pow, map_one]
  let a : ℕ → ℝ := fun k =>
    if 1 ≤ k ∧ k ≤ H then B n (n + k * q)
    else if L - H ≤ k ∧ k < L then B n (n - (L - k) * q)
    else 0
  have hrange_add : ∀ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (s t : ℕ),
      ∑ k ∈ Finset.range (s + t), f k =
        (∑ k ∈ Finset.range s, f k) + ∑ k ∈ Finset.range t, f (s + k) := by
    intro M _ f s t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [← Nat.add_assoc, Finset.sum_range_succ, Finset.sum_range_succ, ih, add_assoc]
  have hIcc_range : ∀ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ),
      ∑ h ∈ Finset.Icc 1 m, f h = ∑ k ∈ Finset.range m, f (k + 1) := by
    intro M _ f m
    induction m with
    | zero => simp
    | succ m ih =>
      have hset : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : m + 1 ∉ Finset.Icc 1 m := by
        simp only [Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert hnotmem, Finset.sum_range_succ, ih, add_comm]
  have hrange_reflect : ∀ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ),
      ∑ k ∈ Finset.range m, f k = ∑ k ∈ Finset.range m, f (m - 1 - k) := by
    intro M _ f m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hsplit : m + 1 = 1 + m := by omega
      have h1 : ∑ k ∈ Finset.range (m + 1), f (m + 1 - 1 - k) =
          f m + ∑ k ∈ Finset.range m, f (m - 1 - k) := by
        rw [hsplit, hrange_add (fun k => f (1 + m - 1 - k)) 1 m]
        have hhead : ∑ k ∈ Finset.range 1, f (1 + m - 1 - k) = f m := by
          rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          have h0 : 1 + m - 1 - 0 = m := by omega
          rw [h0]
        have htail : ∑ k ∈ Finset.range m, f (1 + m - 1 - (1 + k)) =
            ∑ k ∈ Finset.range m, f (m - 1 - k) := by
          apply Finset.sum_congr rfl
          intro k _
          have heq : 1 + m - 1 - (1 + k) = m - 1 - k := by omega
          rw [heq]
        rw [hhead, htail]
      rw [h1, add_comm]
  have hsplit_L : ∀ {M : Type*} [AddCommMonoid M] (g : ℕ → ℝ → M),
      g 0 0 = 0 → (∀ k, g k 0 = 0) →
      (∑ k ∈ Finset.range L, g k (a k)) =
      ∑ h ∈ Finset.Icc 1 H, (g h (B n (n + h * q)) + g (L - h) (B n (n - h * q))) := by
    intro M _ g _ hg0
    have hLdecomp : L = 1 + (H + ((L - 1 - 2 * H) + H)) := by omega
    rw [hLdecomp, hrange_add (fun k => g k (a k)) 1 _,
        hrange_add (fun k => g (1 + k) (a (1 + k))) H _,
        hrange_add (fun k => g (1 + (H + k)) (a (1 + (H + k)))) (L - 1 - 2 * H) H]
    have hp0 : ∑ k ∈ Finset.range 1, g k (a k) = 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have ha0 : a 0 = 0 := by
        dsimp only [a]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [ha0, hg0]
    have hpmid : ∑ k ∈ Finset.range (L - 1 - 2 * H), g (1 + (H + k)) (a (1 + (H + k))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hklt : k < L - 1 - 2 * H := Finset.mem_range.mp hk
      have ham : a (1 + (H + k)) = 0 := by
        dsimp only [a]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [ham, hg0]
    have hppos : ∑ k ∈ Finset.range H, g (1 + k) (a (1 + k)) =
        ∑ h ∈ Finset.Icc 1 H, g h (B n (n + h * q)) := by
      rw [hIcc_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < H := Finset.mem_range.mp hk
      have h1k : 1 + k = k + 1 := by omega
      rw [h1k]
      have hap : a (k + 1) = B n (n + (k + 1) * q) := by
        dsimp only [a]
        rw [if_pos (by omega)]
      rw [hap]
    have hpneg : ∑ k ∈ Finset.range H, g (1 + (H + (L - 1 - 2 * H + k))) (a (1 + (H + (L - 1 - 2 * H + k)))) =
        ∑ h ∈ Finset.Icc 1 H, g (L - h) (B n (n - h * q)) := by
      rw [hrange_reflect _ H, hIcc_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < H := Finset.mem_range.mp hk
      have hidx : 1 + (H + (L - 1 - 2 * H + (H - 1 - k))) = L - (k + 1) := by omega
      rw [hidx]
      have han : a (L - (k + 1)) = B n (n - (k + 1) * q) := by
        dsimp only [a]
        rw [if_neg (by omega), if_pos (by omega)]
        have hsub : L - (L - (k + 1)) = k + 1 := by omega
        rw [hsub]
      rw [han]
    rw [hp0, zero_add, hpmid, zero_add, hppos, hpneg, Finset.sum_add_distrib]
  have hY_eq : ∀ j : ℕ,
      Y n q (z ^ j) - (B n n : ℂ) = ∑ k ∈ Finset.range L, (a k : ℂ) * (z ^ j) ^ k := by
    intro j
    dsimp only [Y]
    rw [add_sub_cancel_left]
    symm
    have hsp := hsplit_L (fun k x => (x : ℂ) * (z ^ j) ^ k) (by simp) (fun _ => by simp)
    rw [hsp]
    apply Finset.sum_congr rfl
    intro h hh
    have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
    have hh2 : h ≤ H := (Finset.mem_Icc.mp hh).2
    have hinv_pow : ((z ^ j)⁻¹) ^ h = (z ^ j) ^ (L - h) := by
      have hzj_ne : z ^ j ≠ 0 := pow_ne_zero j hz_ne
      have hzj_h_ne : (z ^ j) ^ h ≠ 0 := pow_ne_zero h hzj_ne
      have h1 : (z ^ j) ^ h * ((z ^ j)⁻¹) ^ h = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hzj_ne, one_pow]
      have h2 : (z ^ j) ^ h * (z ^ j) ^ (L - h) = 1 := by
        rw [← pow_add]
        have hsum : h + (L - h) = L := by omega
        rw [hsum, ← pow_mul, mul_comm j L, pow_mul, hz_pow, one_pow]
      exact mul_left_cancel₀ hzj_h_ne (h1.trans h2.symm)
    rw [hinv_pow]
  have ha_sq :
      (∑ k ∈ Finset.range L, (a k) ^ 2) =
      ∑ h ∈ Finset.Icc 1 H, ((B n (n + h * q)) ^ 2 + (B n (n - h * q)) ^ 2) :=
    hsplit_L (fun _ x => x ^ 2) (by norm_num) (fun _ => by norm_num)
  have hgeom : ∀ (u : ℂ) (m : ℕ), (u - 1) * ∑ j ∈ Finset.range m, u ^ j = u ^ m - 1 := by
    intro u m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  have horth : ∀ k ∈ Finset.range L, ∀ m ∈ Finset.range L,
      (∑ j ∈ Finset.range L, (z ^ k * (z⁻¹) ^ m) ^ j) = if k = m then (L : ℂ) else 0 := by
    intro k hk m hm
    have hklt : k < L := Finset.mem_range.mp hk
    have hmlt : m < L := Finset.mem_range.mp hm
    by_cases hkm : k = m
    · rw [if_pos hkm, hkm]
      have h1 : z ^ m * (z⁻¹) ^ m = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hz_ne, one_pow]
      rw [h1]
      simp
    · rw [if_neg hkm]
      let u : ℂ := z ^ k * (z⁻¹) ^ m
      have huL : u ^ L = 1 := by
        dsimp only [u]
        rw [mul_pow, ← pow_mul, mul_comm k L, pow_mul, hz_pow, one_pow,
            ← pow_mul, mul_comm m L, pow_mul, hinvL, one_pow, mul_one]
      have hu_ne : u ≠ 1 := by
        intro hu1
        have hzm : z ^ m ≠ 0 := pow_ne_zero m hz_ne
        have hzk_eq_zm : z ^ k = z ^ m := by
          have hmul : (z ^ k * (z⁻¹) ^ m) * z ^ m = 1 * z ^ m := by rw [hu1]
          have hinv : (z⁻¹) ^ m * z ^ m = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hz_ne, one_pow]
          calc
            z ^ k = z ^ k * ((z⁻¹) ^ m * z ^ m) := by rw [hinv, mul_one]
            _ = (z ^ k * (z⁻¹) ^ m) * z ^ m := by ring
            _ = 1 * z ^ m := hmul
            _ = z ^ m := one_mul _
        rcases lt_or_gt_of_ne hkm with hlt | hgt
        · have hdiff : z ^ (m - k) = 1 := by
            have hzk_ne : z ^ k ≠ 0 := pow_ne_zero k hz_ne
            have hadd : k + (m - k) = m := by omega
            have hmul : z ^ k * z ^ (m - k) = z ^ k * 1 := by
              rw [← pow_add, hadd, mul_one, hzk_eq_zm]
            exact mul_left_cancel₀ hzk_ne hmul
          have hdvd : L ∣ m - k := hz.dvd_of_pow_eq_one (m - k) hdiff
          have hle : L ≤ m - k := Nat.le_of_dvd (by omega) hdvd
          omega
        · have hdiff : z ^ (k - m) = 1 := by
            have hadd : m + (k - m) = k := by omega
            have hmul : z ^ m * z ^ (k - m) = z ^ m * 1 := by
              rw [← pow_add, hadd, mul_one, hzk_eq_zm]
            exact mul_left_cancel₀ hzm hmul
          have hdvd : L ∣ k - m := hz.dvd_of_pow_eq_one (k - m) hdiff
          have hle : L ≤ k - m := Nat.le_of_dvd (by omega) hdvd
          omega
      have hprod : (u - 1) * ∑ j ∈ Finset.range L, u ^ j = 0 := by
        rw [hgeom u L, huL, sub_self]
      exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hu_ne)
  have hparseval_C :
      ((∑ j ∈ Finset.range L, ‖Y n q (z ^ j) - (B n n : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ((L : ℝ) * ∑ k ∈ Finset.range L, (a k) ^ 2 : ℝ) := by
    have hnorm_sum :
        ((∑ j ∈ Finset.range L, ‖Y n q (z ^ j) - (B n n : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.range L,
          (∑ k ∈ Finset.range L, (a k : ℂ) * (z ^ j) ^ k) *
          (∑ m ∈ Finset.range L, (a m : ℂ) * ((z⁻¹) ^ j) ^ m) := by
      push_cast
      apply Finset.sum_congr rfl
      intro j _
      rw [hY_eq j, ← Complex.mul_conj']
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [map_mul, Complex.conj_ofReal, map_pow, map_pow, hconj]
    rw [hnorm_sum]
    have hexpand :
        (∑ j ∈ Finset.range L,
          (∑ k ∈ Finset.range L, (a k : ℂ) * (z ^ j) ^ k) *
          (∑ m ∈ Finset.range L, (a m : ℂ) * ((z⁻¹) ^ j) ^ m)) =
        ∑ k ∈ Finset.range L, ∑ m ∈ Finset.range L,
          (a k : ℂ) * (a m : ℂ) * ∑ j ∈ Finset.range L, (z ^ k * (z⁻¹) ^ m) ^ j := by
      have h1 :
          (∑ j ∈ Finset.range L,
            (∑ k ∈ Finset.range L, (a k : ℂ) * (z ^ j) ^ k) *
            (∑ m ∈ Finset.range L, (a m : ℂ) * ((z⁻¹) ^ j) ^ m)) =
          ∑ j ∈ Finset.range L, ∑ k ∈ Finset.range L, ∑ m ∈ Finset.range L,
            (a k : ℂ) * (a m : ℂ) * (z ^ k * (z⁻¹) ^ m) ^ j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm j k, mul_comm j m]
        ring
      rw [h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
    rw [hexpand]
    have hdiag :
        (∑ k ∈ Finset.range L, ∑ m ∈ Finset.range L,
          (a k : ℂ) * (a m : ℂ) * ∑ j ∈ Finset.range L, (z ^ k * (z⁻¹) ^ m) ^ j) =
        ∑ k ∈ Finset.range L, (L : ℂ) * (a k : ℂ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hinner :
          (∑ m ∈ Finset.range L,
            (a k : ℂ) * (a m : ℂ) * ∑ j ∈ Finset.range L, (z ^ k * (z⁻¹) ^ m) ^ j) =
          (a k : ℂ) * (a k : ℂ) * ∑ j ∈ Finset.range L, (z ^ k * (z⁻¹) ^ k) ^ j := by
        apply Finset.sum_eq_single_of_mem k hk
        intro m hm hne
        rw [horth k hk m hm, if_neg (Ne.symm hne), mul_zero]
      rw [hinner, horth k hk k hk, if_pos rfl]
      ring
    rw [hdiag, ← Finset.mul_sum]
    push_cast
    rfl
  have hparseval_R :
      (∑ j ∈ Finset.range L, ‖Y n q (z ^ j) - (B n n : ℂ)‖ ^ 2) =
      (L : ℝ) * ∑ k ∈ Finset.range L, (a k) ^ 2 :=
    Complex.ofReal_injective hparseval_C
  rw [hparseval_R, ha_sq]
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp <;> ring
