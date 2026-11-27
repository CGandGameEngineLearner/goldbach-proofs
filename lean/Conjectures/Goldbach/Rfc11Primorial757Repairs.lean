import Mathlib

/-!
The BLS primality checker and CRT witness encoding are adapted from zhaochengggg's
verified Goldbach PR #3884, commit 88d12c634462fdc8c18bca52d59d4e5cab497ac3.
The certificate data below were generated for the specified interval and every row is rechecked.
-/

namespace Primorial757BLS

/-- Auxiliary loop for `powMod`: structural recursion on fuel, binary method. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, acc, _, _, _ => acc
  | fuel + 1, acc, b, e, m =>
    if e = 0 then acc
    else powModAux fuel (if e % 2 = 1 then acc * b % m else acc) (b * b % m) (e / 2) m

/-- Kernel-friendly modular exponentiation (structural recursion on fuel, binary method). -/
def powMod (a e m : ℕ) : ℕ := powModAux (Nat.log2 e + 1) (1 % m) (a % m) e m

theorem powModAux_eq (fuel : ℕ) : ∀ acc b e m : ℕ, acc % m = acc → e < 2 ^ fuel →
    powModAux fuel acc b e m = acc * b ^ e % m := by
  induction fuel with
  | zero =>
    intro acc b e m hacc he
    have he0 : e = 0 := by simpa using he
    subst he0
    simp [powModAux, hacc]
  | succ n ih =>
    intro acc b e m hacc he
    rw [powModAux]
    have he2 : e / 2 < 2 ^ n := by
      rw [pow_succ] at he
      omega
    split_ifs with h0 h1
    · subst h0
      simp [hacc]
    · rw [ih _ _ _ _ (Nat.mod_mod _ _) he2]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
      have hk : (2 * k + 1) / 2 = k := by omega
      rw [hk]
      have h : acc * b % m * (b * b % m) ^ k ≡ acc * b * (b * b) ^ k [MOD m] :=
        (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
      have h2 : acc * b * (b * b) ^ k = acc * b ^ (2 * k + 1) := by ring
      rw [h2] at h
      exact h
    · rw [ih _ _ _ _ hacc he2]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
      have hk : (2 * k) / 2 = k := by omega
      rw [hk]
      have h : acc * (b * b % m) ^ k ≡ acc * (b * b) ^ k [MOD m] :=
        (Nat.ModEq.refl _).mul ((Nat.mod_modEq _ _).pow _)
      have h2 : acc * (b * b) ^ k = acc * b ^ (2 * k) := by ring
      rw [h2] at h
      exact h

theorem powMod_eq (a e m : ℕ) : powMod a e m = a ^ e % m := by
  unfold powMod
  rw [powModAux_eq _ _ _ _ _ (Nat.mod_mod _ _) Nat.lt_log2_self]
  have h : 1 % m * (a % m) ^ e ≡ 1 * a ^ e [MOD m] :=
    (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
  rw [one_mul] at h
  exact h

/-- Certificate check for `N` with `F = ℓ^e ∣ N - 1` and `N < F^3`.
`a` is the witness base, `s` an integer-square-root witness for the discriminant. -/
def check (N ℓ e a s : ℕ) : Bool :=
  let F := ℓ ^ e
  let x := powMod a ((N - 1) / ℓ) N
  let m := (N - 1) / F
  let c1 := m % F
  let c2 := m / F
  decide (1 < N) && decide (0 < e) && decide (N % F = 1) && decide (N < F * F * F) &&
  decide (powMod x ℓ N = 1) && decide (Nat.gcd (x + N - 1) N = 1) &&
  (decide (N ≤ F * F) || decide (c1 * c1 < 4 * c2) ||
    (decide (s * s + 4 * c2 < c1 * c1) && decide (c1 * c1 < (s + 1) * (s + 1) + 4 * c2)))

/-- If `d ∣ n` but `d ∤ n / ℓ` (`ℓ` prime), then the full `ℓ`-part of `n` divides `d`. -/
theorem pow_dvd_of_dvd_of_not_dvd_div {ℓ e d n : ℕ} (hℓ : ℓ.Prime) (hn : ℓ ^ e ∣ n)
    (hd : d ∣ n) (hnd : ¬ d ∣ n / ℓ) : ℓ ^ e ∣ d := by
  obtain ⟨k, rfl⟩ := hd
  have hk : ¬ ℓ ∣ k := by
    rintro ⟨k', rfl⟩
    apply hnd
    rw [show d * (ℓ * k') = ℓ * (d * k') by ring, Nat.mul_div_cancel_left _ hℓ.pos]
    exact dvd_mul_right _ _
  have hc : Nat.Coprime (ℓ ^ e) k :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hk)
  exact hc.dvd_of_dvd_mul_right hn

/-- Pocklington step: every prime factor of `N` is `≡ 1 (mod ℓ^e)`. -/
theorem prime_factor_dvd_sub_one {N ℓ e a r : ℕ} (hℓ : ℓ.Prime) (hN : 1 < N)
    (hF : ℓ ^ e ∣ N - 1) (he : 0 < e)
    (hx : (a ^ ((N - 1) / ℓ) % N) ^ ℓ % N = 1)
    (hg : Nat.gcd (a ^ ((N - 1) / ℓ) % N + N - 1) N = 1)
    (hr : r.Prime) (hrN : r ∣ N) : ℓ ^ e ∣ r - 1 := by
  have := Fact.mk hr
  have hℓN : ℓ ∣ N - 1 := (dvd_pow_self ℓ he.ne').trans hF
  generalize hxdef : a ^ ((N - 1) / ℓ) % N = x at hx hg
  have hxc : (x : ZMod r) = (a : ZMod r) ^ ((N - 1) / ℓ) := by
    have h1 : (x : ZMod r) = ((a ^ ((N - 1) / ℓ) : ℕ) : ZMod r) := by
      rw [ZMod.natCast_eq_natCast_iff, ← hxdef]
      exact (Nat.mod_modEq _ _).of_dvd hrN
    rw [h1, Nat.cast_pow]
  have hxl : (x : ZMod r) ^ ℓ = 1 := by
    have h1 : ((x ^ ℓ : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      rw [ZMod.natCast_eq_natCast_iff]
      have h2 : x ^ ℓ ≡ 1 [MOD N] := by
        unfold Nat.ModEq
        rw [hx, Nat.mod_eq_of_lt hN]
      exact h2.of_dvd hrN
    simpa using h1
  have hne : (x : ZMod r) ≠ 1 := by
    intro h1
    have h2 : ((x + N - 1 : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, h1, (ZMod.natCast_eq_zero_iff N r).mpr hrN]
      simp
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 := Nat.dvd_gcd h2 hrN
    rw [hg] at h3
    exact hr.one_lt.ne' (Nat.dvd_one.mp h3)
  have hpow : (a : ZMod r) ^ (N - 1) = 1 := by
    rw [← Nat.div_mul_cancel hℓN, pow_mul, ← hxc, hxl]
  have ha0 : (a : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hpow
    exact zero_ne_one hpow
  have hd1 : orderOf (a : ZMod r) ∣ N - 1 := orderOf_dvd_of_pow_eq_one hpow
  have hd2 : ¬ orderOf (a : ZMod r) ∣ (N - 1) / ℓ := by
    rw [orderOf_dvd_iff_pow_eq_one, ← hxc]
    exact hne
  have hd3 : orderOf (a : ZMod r) ∣ r - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha0)
  exact (pow_dvd_of_dvd_of_not_dvd_div hℓ hF hd1 hd2).trans hd3

/-- `(α+β)² - 4αβ = (α-β)²` is a perfect square, so it is neither negative nor strictly
between two consecutive squares. -/
theorem square_gap {α β s : ℕ} :
    ¬ ((α + β) * (α + β) < 4 * (α * β)) ∧
    ¬ (s * s + 4 * (α * β) < (α + β) * (α + β) ∧
      (α + β) * (α + β) < (s + 1) * (s + 1) + 4 * (α * β)) := by
  have key : ∀ a d : ℕ,
      ¬ ((a + (a + d)) * (a + (a + d)) < 4 * (a * (a + d))) ∧
      ¬ (s * s + 4 * (a * (a + d)) < (a + (a + d)) * (a + (a + d)) ∧
        (a + (a + d)) * (a + (a + d)) < (s + 1) * (s + 1) + 4 * (a * (a + d))) := by
    intro a d
    have hid : (a + (a + d)) * (a + (a + d)) = d * d + 4 * (a * (a + d)) := by ring
    rw [hid]
    refine ⟨by omega, ?_⟩
    rintro ⟨h1, h2⟩
    have h1' : s * s < d * d := by omega
    have h2' : d * d < (s + 1) * (s + 1) := by omega
    have hsd : s < d := by
      by_contra hc
      have := Nat.mul_le_mul (Nat.le_of_not_lt hc) (Nat.le_of_not_lt hc)
      omega
    have hds : d < s + 1 := by
      by_contra hc
      have := Nat.mul_le_mul (Nat.le_of_not_lt hc) (Nat.le_of_not_lt hc)
      omega
    omega
  rcases le_total α β with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact key α d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := key β d
    rwa [Nat.add_comm (β + d) β, Nat.mul_comm (β + d) β]

theorem check_sound {N ℓ e a s : ℕ} (hℓ : ℓ.Prime) (h : check N ℓ e a s = true) : N.Prime := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, powMod_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hN, he⟩, hmod⟩, hlt⟩, hx⟩, hg⟩, hsq⟩ := h
  generalize hFdef : ℓ ^ e = F at hmod hlt hsq
  have hFpos : 0 < F := by
    rw [← hFdef]
    exact pow_pos hℓ.pos e
  have hF : F ∣ N - 1 := by
    have h1 := Nat.dvd_sub_mod (n := F) N
    rwa [hmod] at h1
  by_contra hNp
  have hr : (N.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨t, ht⟩ := Nat.minFac_dvd N
  generalize N.minFac = r at hr ht
  have hrF : F ∣ r - 1 := by
    rw [← hFdef]
    exact prime_factor_dvd_sub_one hℓ hN (hFdef ▸ hF) he hx hg hr (Dvd.intro t ht.symm)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at ht
    exact hNp (ht ▸ hr)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    omega
  obtain ⟨α, hα⟩ := hrF
  have hr2 := hr.two_le
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hα
    omega
  have hrα : r = F * α + 1 := by omega
  have htF : F ∣ t - 1 := by
    have h1 : N - 1 = F * (α * t) + (t - 1) := by
      have h2 : N = F * (α * t) + t := by
        rw [ht, hrα]
        ring
      omega
    rw [h1] at hF
    exact (Nat.dvd_add_right (dvd_mul_right F (α * t))).mp hF
  obtain ⟨β, hβ⟩ := htF
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hβ
    omega
  have htβ : t = F * β + 1 := by omega
  have hNeq : N = α * β * (F * F) + (α + β) * F + 1 := by
    rw [ht, hrα, htβ]
    ring
  have hαβpos : 1 ≤ α * β := Nat.mul_pos (Nat.pos_of_ne_zero hα0) (Nat.pos_of_ne_zero hβ0)
  have hαβ : α * β < F := by
    by_contra hc
    have h1 : F * (F * F) ≤ α * β * (F * F) := Nat.mul_le_mul_right _ (Nat.le_of_not_lt hc)
    have h2 : F * F * F = F * (F * F) := by ring
    have h3 := Nat.zero_le ((α + β) * F)
    omega
  have hNbig : F * F < N := by
    have h1 : 1 * (F * F) ≤ α * β * (F * F) := Nat.mul_le_mul_right _ hαβpos
    have h3 := Nat.zero_le ((α + β) * F)
    omega
  have hsum1 : α + β ≤ α * β + 1 := by
    obtain ⟨a', rfl⟩ : ∃ a', α = a' + 1 := ⟨α - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', β = b' + 1 := ⟨β - 1, by omega⟩
    have h1 : (a' + 1) * (b' + 1) = a' * b' + a' + b' + 1 := by ring
    omega
  have hsum : α + β < F := by
    by_contra hc
    have h1 : α + β = F := by omega
    have h2 : α * β + 1 = F := by omega
    have h3 : N = F * F * F + 1 := by
      calc N = α * β * (F * F) + (α + β) * F + 1 := hNeq
        _ = (α * β + 1) * (F * F) + 1 := by rw [h1]; ring
        _ = F * F * F + 1 := by rw [h2]; ring
    omega
  have hm : (N - 1) / F = (α + β) + F * (α * β) := by
    apply Nat.div_eq_of_eq_mul_right hFpos
    have h1 : α * β * (F * F) + (α + β) * F = F * ((α + β) + F * (α * β)) := by ring
    omega
  have hc1 : (N - 1) / F % F = α + β := by
    rw [hm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsum]
  have hc2 : (N - 1) / F / F = α * β := by
    rw [hm, Nat.add_mul_div_left _ _ hFpos, Nat.div_eq_of_lt hsum, zero_add]
  rw [hc1, hc2] at hsq
  have hgap := square_gap (α := α) (β := β) (s := s)
  rcases hsq with (h1 | h1) | h1
  · omega
  · exact hgap.1 h1
  · exact hgap.2 h1

end Primorial757BLS

namespace Primorial757Rows
open Primorial757BLS

def lOf (i : ℕ) : ℕ :=
  match i with
  | 0 => 3 | 1 => 5 | 2 => 7 | 3 => 11 | 4 => 13 | 5 => 17 | 6 => 19 | _ => 23

theorem lOf_prime (i : ℕ) : (lOf i).Prime := by
  unfold lOf
  split <;> norm_num

def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, x, _ => x
  | f + 1, x, n => if (x + n / x) / 2 < x then isqrtAux f ((x + n / x) / 2) n else x

def isqrt (n : ℕ) : ℕ := if n = 0 then 0 else isqrtAux 64 (2 ^ (Nat.log2 n / 2 + 1)) n

def sWit (N l e : ℕ) : ℕ :=
  isqrt (((N - 1) / l ^ e % l ^ e) * ((N - 1) / l ^ e % l ^ e) - 4 * ((N - 1) / l ^ e / l ^ e))

def bLoop : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, b, _, _ => b
  | f + 1, b, l, n => if n < l ^ (3 * b) then b else bLoop f (b + 1) l n

def pOf (n l b e k : ℕ) : ℕ :=
  1 + 2 ^ e * ((n - 2) * powMod (2 ^ e) (l ^ (b - 1) * (l - 1) - 1) (l ^ b) % l ^ b) + k * (2 ^ e * l ^ b)

def rowAux (n l b e a1 a2 p : ℕ) : Bool :=
  decide (p ≤ n) && check p 2 e a1 (sWit p 2 e) && check (n - p) l b a2 (sWit (n - p) l b)

def rowOK (n code : ℕ) : Bool :=
  rowAux n (lOf (code % 8)) (bLoop 400 1 (lOf (code % 8)) n) (Nat.log2 n / 3 + 1)
    (code / 512 % 64) (code / 8 % 64)
    (pOf n (lOf (code % 8)) (bLoop 400 1 (lOf (code % 8)) n) (Nat.log2 n / 3 + 1) (code / 32768))

theorem rowOK_sound {n code : ℕ} (h : rowOK n code = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  unfold rowOK rowAux at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, h1⟩, h2⟩ := h
  exact ⟨_, _, check_sound Nat.prime_two h1, check_sound (lOf_prime _) h2, Nat.add_sub_of_le hp⟩

def checkList (f : ℕ → ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, c :: cs => rowOK (f i) c && checkList f (i + 1) cs

theorem checkList_sound (f : ℕ → ℕ) : ∀ (cs : List ℕ) (i0 : ℕ), checkList f i0 cs = true →
    ∀ i, i0 ≤ i → i < i0 + cs.length → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = f i := by
  intro cs
  induction cs with
  | nil =>
    intro i0 _ i h1 h2
    simp only [List.length_nil] at h2
    omega
  | cons c cs ih =>
    intro i0 h i h1 h2
    simp only [checkList, Bool.and_eq_true] at h
    simp only [List.length_cons] at h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact rowOK_sound h.1
    · exact ih (i0 + 1) h.2 i hlt (by omega)



end Primorial757Rows

namespace Primorial757

def registryW : ℕ := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p
def W : ℕ := 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507212970

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
theorem registryW_eq_W : registryW = W := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
theorem cutoff : 6 * W < 10^316 ∧ (10:ℕ)^316 < 7 * W := by decide +kernel

private theorem W_large : 1514 < W := by decide +kernel

theorem small_prime_obstruction {k p : ℕ} (hk : 1 ≤ k) (hp : p ≤ 757) (hPrime : p.Prime) :
    ¬ (k * W - p).Prime := by
  have hm : p ∈ (Finset.range 758).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hPrime⟩
  have hd : p ∣ registryW := Finset.dvd_prod_of_mem (fun n : ℕ => n) hm
  rw [registryW_eq_W] at hd
  have hd' : p ∣ k * W - p := Nat.dvd_sub (dvd_mul_of_dvd_right hd k) (dvd_refl p)
  have hW : W ≤ k * W := by
    simpa using Nat.mul_le_mul_right W hk
  have hpLt : p < k * W - p := by
    have := W_large
    omega
  intro hn
  rcases hn.eq_one_or_self_of_dvd p hd' with hOne | hEqual
  · exact hPrime.ne_one hOne
  · exact (Nat.ne_of_lt hpLt) hEqual

end Primorial757

namespace Primorial757

private def target (i : ℕ) : ℕ := (i+1)*W
private def codes : List ℕ := [134448680, 245302800, 251397648, 21235240, 112035344, 412321296]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem witnesses_checked : Primorial757Rows.checkList target 0 codes = true := by
  decide +kernel

theorem witnesses {k : ℕ} (hlo : 1≤k) (hhi : k≤6) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=k*W := by
  have hlt : k-1 < 0+codes.length := by
    have hlen : codes.length = 6 := by decide +kernel
    omega
  obtain ⟨p,q,hp,hq,h⟩ := Primorial757Rows.checkList_sound target codes 0 witnesses_checked
    (k-1) (Nat.zero_le _) hlt
  have hk : k-1+1=k := by omega
  exact ⟨p,q,hp,hq,by simpa only [target, hk] using h⟩

end Primorial757

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
theorem Conjectures.Goldbach.Rfc11Primorial757Repairs :
    let W := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p; 6*W < 10^316 ∧ (10:ℕ)^316 < 7*W ∧ (∀ k : ℕ, 1≤k → k≤6 → let n := k*W; (∀ p≤757, p.Prime → ¬ (n-p).Prime) ∧ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)) := by
  dsimp only
  rw [show (∏ p ∈ (Finset.range 758).filter Nat.Prime, p) = Primorial757.W from
    Primorial757.registryW_eq_W]
  refine ⟨Primorial757.cutoff.1, Primorial757.cutoff.2, ?_⟩
  intro k hlo hhi
  exact ⟨fun _ hp hpPrime => Primorial757.small_prime_obstruction hlo hp hpPrime,
    Primorial757.witnesses hlo hhi⟩
