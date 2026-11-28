import Mathlib

/-! 数字词题的基础层：B 进制低位数字在"前插高位块"下不变，
以及从词里读出首位。 -/

namespace DigitWords

variable {B : ℕ}

lemma Bpos (hB : 2 ≤ B) : 0 < B := by omega

/-- 高位块 `d * B^p` 不影响 `B^i`（`i < p`）以下的数字提取。 -/
lemma div_mod_digit (hB : 2 ≤ B) (d r p i : ℕ) (hp : i < p) :
    (d * B ^ p + r) / B ^ i % B = r / B ^ i % B := by
  have hB0 : 0 < B := Bpos hB
  have hBipos : 0 < B ^ i := Nat.pow_pos hB0
  have hle : i ≤ p := le_of_lt hp
  have hBp : B ^ p = B ^ i * B ^ (p - i) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hle]
  have hx : d * B ^ p = B ^ i * (d * B ^ (p - i)) := by
    rw [hBp]; ring
  have hdiv : (d * B ^ p + r) / B ^ i = d * B ^ (p - i) + r / B ^ i := by
    rw [hx, Nat.add_comm, Nat.add_mul_div_left _ _ hBipos, Nat.add_comm]
  have hBdvd : B ∣ d * B ^ (p - i) := by
    have hp1 : 1 ≤ p - i := by omega
    have h1 : B ^ 1 ∣ B ^ (p - i) := Nat.pow_dvd_pow B hp1
    have h2 : B ∣ B ^ (p - i) := by simpa using h1
    exact dvd_mul_of_dvd_right h2 d
  rw [hdiv, Nat.add_mod, Nat.mod_eq_zero_of_dvd hBdvd, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ hB0)

/-- 分解：商是首位，余数是尾块。 -/
lemma div_digit_self (hB : 2 ≤ B) (d r p : ℕ) (hr : r < B ^ p) :
    (d * B ^ p + r) / B ^ p = d ∧ (d * B ^ p + r) % B ^ p = r := by
  have hB0 : 0 < B := Bpos hB
  have hBp : 0 < B ^ p := Nat.pow_pos hB0
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm d (B ^ p), Nat.mul_add_div hBp, Nat.div_eq_of_lt hr]
    omega
  · rw [Nat.mul_comm d (B ^ p), Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- 首位数字。 -/
lemma top_digit (hB : 2 ≤ B) (d r p : ℕ) (hr : r < B ^ p) (hd : d < B) :
    (d * B ^ p + r) / B ^ p % B = d := by
  rw [(div_digit_self hB d r p hr).1, Nat.mod_eq_of_lt hd]

/-- 分解唯一。 -/
lemma decomp_inj (hB : 2 ≤ B) {d d' r r' p : ℕ}
    (hr : r < B ^ p) (hr' : r' < B ^ p)
    (h : d * B ^ p + r = d' * B ^ p + r') : d = d' ∧ r = r' := by
  have h1 := div_digit_self hB d r p hr
  have h2 := div_digit_self hB d' r' p hr'
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

end DigitWords

theorem Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * (↑x1 * x2)) * Complex.I); have x2 : ℕ → Finset ℕ → ℕ → Finset ℕ := fun (x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ) => {x5 ∈ Finset.range (x2 ^ x4) | (∀ x6 < x4, x5 / x2 ^ x6 % x2 ∈ x3) ∧ ∀ x6 < x4 - (1 : ℕ), x5 / x2 ^ x6 % x2 ≠ x5 / x2 ^ (x6 + (1 : ℕ)) % x2}; have x3 : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : Finset ℕ) (x5 : ℕ) => Nat.rec (motive := fun (x6 : ℕ) => ℕ → ℝ → ℂ) x1 (fun (x6 : ℕ) (x7 : ℕ → ℝ → ℂ) (x8 : ℕ) (x9 : ℝ) => x1 (x8 * x3 ^ (x6 + (1 : ℕ))) x9 * ∑ x10 ∈ x4 with x10 ≠ x8, x7 x10 x9) x5; ∀ (x4 : ℕ), (2 : ℕ) ≤ x4 → ∀ x6 ⊆ Finset.range x4, (2 : ℕ) ≤ x6.card → ∀ (x9 : ℕ), (∀ (x10 : ℝ), ∑ x11 ∈ x2 x4 x6 (x9 + (1 : ℕ)), x1 x11 x10 = ∑ x11 ∈ x6, x3 x4 x6 x9 x11 x10) ∧ (x2 x4 x6 (x9 + (1 : ℕ))).card = x6.card * (x6.card - (1 : ℕ)) ^ x9) := by

  intro x1 x2 x3 B hB D hD hD2 K
  have hB0 : 0 < B := by omega
  have memW : ∀ (m : ℕ) (w : ℕ), w ∈ x2 B D m ↔
      w < B ^ m ∧ (∀ i < m, w / B ^ i % B ∈ D) ∧
        (∀ i < m - 1, w / B ^ i % B ≠ w / B ^ (i + 1) % B) := by
    intro m w
    simp only [x2, Finset.mem_filter, Finset.mem_range]
  have g_zero : ∀ (a : ℕ) (t : ℝ), x3 B D 0 a t = x1 a t := by
    intro a t
    rfl
  have g_succ : ∀ (j a : ℕ) (t : ℝ),
      x3 B D (j + 1) a t
        = x1 (a * B ^ (j + 1)) t * ∑ d ∈ D with d ≠ a, x3 B D j d t := by
    intro j a t
    rfl
  have W_one : x2 B D 1 = D := by
    ext w
    rw [memW 1 w]
    constructor
    · rintro ⟨hlt, hin, -⟩
      have hwB : w < B := by simpa using hlt
      have h := hin 0 (by norm_num)
      simp only [Nat.pow_zero, Nat.div_one] at h
      rwa [Nat.mod_eq_of_lt hwB] at h
    · intro hw
      have hwB : w < B := Finset.mem_range.mp (hD hw)
      refine ⟨by simpa using hwB, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp only [Nat.pow_zero, Nat.div_one]
        rw [Nat.mod_eq_of_lt hwB]
        exact hw
      · intro i hi
        omega
  -- 字符的乘性：χ(m+n) = χ m · χ n
  have chi_add : ∀ (m n : ℕ) (t : ℝ), x1 (m + n) t = x1 m t * x1 n t := by
    intro m n t
    simp only [x1]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- 粘合（前向）：高位块 a 与合法尾块拼成一个词
  have glue_mem : ∀ (m a r : ℕ), a ∈ D → r ∈ x2 B D (m + 1) → r / B ^ m % B ≠ a →
      a * B ^ (m + 1) + r ∈ x2 B D (m + 2) := by
    intro m a r ha hr hne
    have harange : a < B := Finset.mem_range.mp (hD ha)
    have hpow : 0 < B ^ (m + 1) := Nat.pow_pos hB0
    rw [memW (m + 2) (a * B ^ (m + 1) + r)] at *
    rw [memW (m + 1) r] at hr
    obtain ⟨hrlt, hrdig, hradj⟩ := hr
    refine ⟨?_, ?_, ?_⟩
    · have h1 : a * B ^ (m + 1) + r < a * B ^ (m + 1) + B ^ (m + 1) :=
        Nat.add_lt_add_left hrlt _
      have h2 : a * B ^ (m + 1) + B ^ (m + 1) = (a + 1) * B ^ (m + 1) := by ring
      have h3 : (a + 1) * B ^ (m + 1) ≤ B * B ^ (m + 1) := Nat.mul_le_mul_right _ (by omega)
      have h4 : B * B ^ (m + 1) = B ^ (m + 2) := by
        rw [Nat.mul_comm, ← Nat.pow_succ]
      omega
    · intro i hi
      rcases Nat.lt_or_eq_of_le (show i ≤ m + 1 by omega) with hlt | heq
      · rw [DigitWords.div_mod_digit hB a r (m + 1) i hlt]
        exact hrdig i (by omega)
      · rw [heq]
        rw [DigitWords.top_digit hB a r (m + 1) hrlt harange]
        exact ha
    · intro i hi
      rcases Nat.lt_or_eq_of_le (show i ≤ m by omega) with hlt | heq
      · rw [DigitWords.div_mod_digit hB a r (m + 1) i (by omega),
          DigitWords.div_mod_digit hB a r (m + 1) (i + 1) (by omega)]
        exact hradj i hlt
      · rw [heq, DigitWords.div_mod_digit hB a r (m + 1) m (by omega),
          DigitWords.top_digit hB a r (m + 1) hrlt harange]
        exact hne

  -- 反解：任意词按首位唯一拆成 (a, 尾块)
  have glue_converse : ∀ (m : ℕ) (w : ℕ), w ∈ x2 B D (m + 2) →
      w / B ^ (m + 1) < B ∧ (w / B ^ (m + 1)) ∈ D ∧
      (w % B ^ (m + 1)) ∈ x2 B D (m + 1) ∧
      (w % B ^ (m + 1)) / B ^ m % B ≠ w / B ^ (m + 1) ∧
      w = w / B ^ (m + 1) * B ^ (m + 1) + w % B ^ (m + 1) := by
    intro m w hw
    rw [memW (m + 2) w] at hw
    obtain ⟨hlt, hdig, hadj⟩ := hw
    have ha_lt : w / B ^ (m + 1) < B := by
      have h1 : w < B ^ (m + 1) * B := by
        rw [← Nat.pow_succ]
        exact hlt
      exact Nat.div_lt_of_lt_mul h1
    have haD : w / B ^ (m + 1) ∈ D := by
      have h := hdig (m + 1) (by omega)
      rwa [Nat.mod_eq_of_lt ha_lt] at h
    have hrlt : w % B ^ (m + 1) < B ^ (m + 1) :=
      Nat.mod_lt _ (Nat.pow_pos hB0)
    have hdecomp : w = w / B ^ (m + 1) * B ^ (m + 1) + w % B ^ (m + 1) := by
      have h := Nat.div_add_mod w (B ^ (m + 1))
      rw [Nat.mul_comm] at h
      omega
    refine ⟨ha_lt, haD, ?_, ?_, hdecomp⟩
    · -- 尾块是长度 m+1 的词
      rw [memW (m + 1) (w % B ^ (m + 1))]
      refine ⟨hrlt, ?_, ?_⟩
      · intro i hi
        have h1 := DigitWords.div_mod_digit hB (w / B ^ (m + 1)) (w % B ^ (m + 1)) (m + 1) i hi
        rw [← hdecomp] at h1
        rw [← h1]
        exact hdig i (by omega)
      · intro i hi
        have h1 := DigitWords.div_mod_digit hB (w / B ^ (m + 1)) (w % B ^ (m + 1)) (m + 1) i (by omega)
        have h2 := DigitWords.div_mod_digit hB (w / B ^ (m + 1)) (w % B ^ (m + 1)) (m + 1) (i + 1) (by omega)
        rw [← hdecomp] at h1 h2
        rw [← h1, ← h2]
        exact hadj i (by omega)
    · -- 尾块首位与 a 不同（拼接处的邻接）
      have h1 := DigitWords.div_mod_digit hB (w / B ^ (m + 1)) (w % B ^ (m + 1)) (m + 1) m (by omega)
      rw [← hdecomp] at h1
      rw [← h1]
      have h2 := hadj m (by omega)
      rw [Nat.mod_eq_of_lt ha_lt] at h2
      exact h2

  -- 粘合：整族词 = 各首位纤维的不交并
  have W_glue : ∀ (m : ℕ), x2 B D (m + 2) =
      D.biUnion (fun a => ((x2 B D (m + 1)).filter (fun r => r / B ^ m % B ≠ a)).image
        (fun r => a * B ^ (m + 1) + r)) := by
    intro m
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hw
      obtain ⟨-, haD, hrW, hne, hdec⟩ := glue_converse m w hw
      exact ⟨_, haD, _, ⟨hrW, hne⟩, hdec.symm⟩
    · rintro ⟨a, haD, r, ⟨hrW, hne⟩, hw⟩
      rw [← hw]
      exact glue_mem m a r haD hrW hne
  -- 各纤维互不相交（首位不同）
  have W_disj : ∀ (m : ℕ), ∀ a ∈ D, ∀ a' ∈ D, a ≠ a' →
      Disjoint (((x2 B D (m + 1)).filter (fun r => r / B ^ m % B ≠ a)).image (fun r => a * B ^ (m + 1) + r))
        (((x2 B D (m + 1)).filter (fun r => r / B ^ m % B ≠ a')).image (fun r => a' * B ^ (m + 1) + r)) := by
    intro m a ha a' ha' hne
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_image, Finset.mem_filter] at hw1 hw2
    obtain ⟨r1, ⟨hr1W, -⟩, hw1eq⟩ := hw1
    obtain ⟨r2, ⟨hr2W, -⟩, hw2eq⟩ := hw2
    have harange : a < B := Finset.mem_range.mp (hD ha)
    have ha'range : a' < B := Finset.mem_range.mp (hD ha')
    have hr1 : r1 < B ^ (m + 1) := ((memW (m + 1) r1).mp hr1W).1
    have hr2 : r2 < B ^ (m + 1) := ((memW (m + 1) r2).mp hr2W).1
    have htop1 := DigitWords.top_digit hB a r1 (m + 1) hr1 harange
    have htop2 := DigitWords.top_digit hB a' r2 (m + 1) hr2 ha'range
    -- w 同时等于 a*…+r1 与 a'*…+r2，取首位即得 a = a'
    have heqe : a * B ^ (m + 1) + r1 = a' * B ^ (m + 1) + r2 := by rw [hw1eq, hw2eq]
    have hfin : (a * B ^ (m + 1) + r1) / B ^ (m + 1) % B
        = (a' * B ^ (m + 1) + r2) / B ^ (m + 1) % B := by rw [heqe]
    rw [htop1, htop2] at hfin
    exact hne hfin
  -- 按首位分区的两件事实（与 k 无关）
  have W_split : ∀ (m : ℕ), x2 B D (m + 1) =
      D.biUnion (fun a => (x2 B D (m + 1)).filter (fun r => r / B ^ m % B = a)) := by
    intro m
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hw
      exact ⟨w / B ^ m % B, ((memW (m + 1) w).mp hw).2.1 m (by omega), hw, rfl⟩
    · rintro ⟨a, -, hw, -⟩
      exact hw
  have W_split_disj : ∀ (m : ℕ), ∀ a ∈ D, ∀ a' ∈ D, a ≠ a' →
      Disjoint ((x2 B D (m + 1)).filter (fun r => r / B ^ m % B = a))
        ((x2 B D (m + 1)).filter (fun r => r / B ^ m % B = a')) := by
    intro m a ha a' ha' hne
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_filter] at hw1 hw2
    exact hne (hw1.2.symm.trans hw2.2)
  -- 主归纳：逐位字符和 + 总计数
  have key : ∀ k : ℕ,
      (∀ a ∈ D, ∀ t : ℝ,
          ∑ w ∈ (x2 B D (k + 1)).filter (fun w => w / B ^ k % B = a), x1 w t = x3 B D k a t) ∧
        (x2 B D (k + 1)).card = D.card * (D.card - 1) ^ k := by
    intro k
    induction k with
    | zero =>
        constructor
        · intro a ha t
          have hfilter : (x2 B D (0 + 1)).filter (fun w => w / B ^ 0 % B = a) = {a} := by
            rw [Nat.zero_add, W_one]
            ext w
            simp only [Finset.mem_filter, Finset.mem_singleton, Nat.pow_zero, Nat.div_one]
            constructor
            · rintro ⟨hw, hwa⟩
              have hwB : w < B := Finset.mem_range.mp (hD hw)
              rwa [Nat.mod_eq_of_lt hwB] at hwa
            · rintro rfl
              exact ⟨ha, Nat.mod_eq_of_lt (Finset.mem_range.mp (hD ha))⟩
          rw [hfilter, Finset.sum_singleton, g_zero]
        · simp only [Nat.zero_add, W_one, pow_zero, mul_one]
    | succ k ih =>
        constructor
        · -- 逐位字符和
          intro a ha t
          have harange : a < B := Finset.mem_range.mp (hD ha)
          have himg : (x2 B D (k + 2)).filter (fun w => w / B ^ (k + 1) % B = a)
              = ((x2 B D (k + 1)).filter (fun r => r / B ^ k % B ≠ a)).image
                  (fun r => a * B ^ (k + 1) + r) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_image]
            constructor
            · rintro ⟨hw, htop⟩
              obtain ⟨hlt, -, hrW, hne0, hdec⟩ := glue_converse k w hw
              have hwtop : w / B ^ (k + 1) = a := by
                rwa [Nat.mod_eq_of_lt hlt] at htop
              have himg_eq : a * B ^ (k + 1) + w % B ^ (k + 1) = w := by
                rw [← hwtop]
                exact hdec.symm
              exact ⟨w % B ^ (k + 1), ⟨hrW, by rw [← hwtop]; exact hne0⟩, himg_eq⟩
            · rintro ⟨r, ⟨hrW, hne⟩, rfl⟩
              have hr : r < B ^ (k + 1) := ((memW (k + 1) r).mp hrW).1
              exact ⟨glue_mem k a r ha hrW hne,
                DigitWords.top_digit hB a r (k + 1) hr harange⟩
          rw [himg, Finset.sum_image]
          · have hchi : ∀ r, x1 (a * B ^ (k + 1) + r) t
                = x1 (a * B ^ (k + 1)) t * x1 r t :=
              fun r => chi_add (a * B ^ (k + 1)) r t
            simp only [hchi]
            rw [← Finset.mul_sum]
            have hTsum : ∑ r ∈ (x2 B D (k + 1)).filter (fun r => r / B ^ k % B ≠ a), x1 r t
                = ∑ d ∈ D.erase a, x3 B D k d t := by
              have hsplit : (x2 B D (k + 1)).filter (fun r => r / B ^ k % B ≠ a)
                  = (D.erase a).biUnion (fun d =>
                      (x2 B D (k + 1)).filter (fun r => r / B ^ k % B = d)) := by
                ext r
                simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_erase]
                constructor
                · intro hr
                  have hdD : r / B ^ k % B ∈ D := ((memW (k + 1) r).mp hr.1).2.1 k (by omega)
                  exact ⟨r / B ^ k % B, ⟨hr.2, hdD⟩, hr.1, rfl⟩
                · rintro ⟨d, ⟨hne, -⟩, hr, hrd⟩
                  exact ⟨hr, by rw [hrd]; exact hne⟩
              rw [hsplit, Finset.sum_biUnion (fun d hd d' hd' hne =>
                W_split_disj k d (Finset.mem_of_mem_erase hd) d'
                  (Finset.mem_of_mem_erase hd') hne)]
              exact Finset.sum_congr rfl (fun d hd =>
                ih.1 d (Finset.mem_of_mem_erase hd) t)
            rw [hTsum]
            have hfinset : D.erase a = D.filter (fun d => d ≠ a) := by
              ext d
              simp only [Finset.mem_erase, Finset.mem_filter]
              tauto
            rw [hfinset, g_succ]
          · intro x _ y _ hxy
            dsimp only at hxy
            exact Nat.add_left_cancel hxy
        · -- 计数（同前）
          calc (x2 B D (k + 2)).card
              = ∑ a ∈ D, (((x2 B D (k + 1)).filter (fun r => r / B ^ k % B ≠ a)).card) := by
                rw [W_glue k, Finset.card_biUnion]
                · refine Finset.sum_congr rfl (fun a ha => ?_)
                  rw [Finset.card_image_of_injOn]
                  intro x _ y _ hxy
                  dsimp only at hxy
                  exact Nat.add_left_cancel hxy
                · intro a ha a' ha' hne
                  exact W_disj k a ha a' ha' hne
            _ = ∑ a ∈ D, ∑ r ∈ x2 B D (k + 1), (if r / B ^ k % B ≠ a then 1 else 0) := by
                refine Finset.sum_congr rfl (fun a ha => ?_)
                exact Finset.card_filter (fun r => r / B ^ k % B ≠ a) (x2 B D (k + 1))
            _ = ∑ r ∈ x2 B D (k + 1), ∑ a ∈ D, (if r / B ^ k % B ≠ a then 1 else 0) := by
                rw [Finset.sum_comm]
            _ = ∑ r ∈ x2 B D (k + 1), (D.card - 1) := by
                refine Finset.sum_congr rfl (fun r hr => ?_)
                have hdD : r / B ^ k % B ∈ D := ((memW (k + 1) r).mp hr).2.1 k (by omega)
                have hfil : D.filter (fun a => r / B ^ k % B ≠ a) = D.erase (r / B ^ k % B) := by
                  ext a
                  simp only [Finset.mem_filter, Finset.mem_erase]
                  constructor
                  · rintro ⟨ha, hne⟩; exact ⟨Ne.symm hne, ha⟩
                  · rintro ⟨hne, ha⟩; exact ⟨ha, Ne.symm hne⟩
                rw [Finset.sum_boole, hfil, Finset.card_erase_of_mem hdD]
                simp
            _ = (x2 B D (k + 1)).card * (D.card - 1) := by
                rw [Finset.sum_const, nsmul_eq_mul]
                simp
            _ = D.card * (D.card - 1) ^ (k + 1) := by
                rw [ih.2, Nat.pow_succ]
                ring
  obtain ⟨hper, hcardK⟩ := key K
  constructor
  · -- 总字符和 = 各首位纤维之和
    intro t
    rw [W_split K, Finset.sum_biUnion (fun a ha a' ha' hne =>
      W_split_disj K a ha a' ha' hne)]
    exact Finset.sum_congr rfl (fun a ha => hper a ha t)
  · exact hcardK
