import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_moving_window_floor :
    let block := fun x : ℕ => Finset.Ioc x (2*x);
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301);
    let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n^2+a)).card;
    ∀ x q : ℕ, 0<q → |(countHits 1 x q : ℝ) - ((window x q).card : ℝ)*((roots 1 q).card : ℝ)/q| ≤ ((roots 1 q).card : ℝ) := by
  let block := fun x : ℕ => Finset.Ioc x (2*x)
  let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a)
  let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301)
  let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n^2+a)).card
  show ∀ x q : ℕ, 0<q → |(countHits 1 x q : ℝ) - ((window x q).card : ℝ)*((roots 1 q).card : ℝ)/q| ≤ ((roots 1 q).card : ℝ)
  classical
  intro x q hq
  haveI : NeZero q := ⟨by omega⟩
  have hqpos : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr hq
  have memroots : ∀ n : ℕ, n ∈ roots 1 q ↔ n < q ∧ q ∣ n^2+1 := by
    intro n
    simp [roots, Finset.mem_filter, Finset.mem_range]
  -- exact count of one residue class in an initial segment
  have range_card : ∀ L r : ℕ, r < q →
      ((Finset.range L).filter (fun k => k % q = r)).card = (L + q - 1 - r)/q := by
    intro L r hr
    rw [← Finset.card_range ((L + q - 1 - r)/q)]
    refine Finset.card_bij (fun k _ => k / q) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkL, hkmod⟩ := hk
      simp only [Finset.mem_range]
      have hdiv := Nat.div_add_mod k q
      have hkr : k / q * q = k - r := by
        rw [Nat.mul_comm, ← hkmod]
        omega
      have hkge : r ≤ k := by omega
      rw [Nat.lt_div_iff_mul_lt hq, hkr]
      have hsub : (L + q - 1 - r) - (q - 1) = L - r := by omega
      rw [hsub]
      omega
    · intro k1 h1 k2 h2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at h1 h2
      have e1 : q*(k1/q) + r = k1 := by
        rw [← h1.2]; exact Nat.div_add_mod k1 q
      have e2 : q*(k2/q) + r = k2 := by
        rw [← h2.2]; exact Nat.div_add_mod k2 q
      rw [heq] at e1
      omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      have hb : (m+1)*q ≤ L + q - 1 - r := by
        have h := (Nat.le_div_iff_mul_le hq).mp (Nat.succ_le_of_lt hm)
        simpa using h
      have hmq : (m+1)*q = m*q + q := by ring
      refine ⟨r + m*q, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, ?_⟩
        · rw [hmq] at hb
          omega
        · rw [Nat.add_mul_mod_self_right]
          exact Nat.mod_eq_of_lt hr
      · have h1 : m*q ≤ r + m*q := Nat.le_add_left _ _
        have h2 : r + m*q < (m+1)*q := by
          rw [hmq]; omega
        exact Nat.div_eq_of_lt_le h1 h2
  have div_diff : ∀ A B : ℕ, B ≤ A →
      |(((A/q : ℕ)) : ℝ) - (((B/q : ℕ)) : ℝ) - ((A - B : ℕ) : ℝ)/q| ≤ 1 := by
    intro A B hBA
    have hA : (q:ℝ)*(((A/q:ℕ)):ℝ) + (((A%q:ℕ)):ℝ) = (A:ℝ) := by
      have h := Nat.div_add_mod A q
      rw [← Nat.cast_mul, ← Nat.cast_add, h]
    have hB : (q:ℝ)*(((B/q:ℕ)):ℝ) + (((B%q:ℕ)):ℝ) = (B:ℝ) := by
      have h := Nat.div_add_mod B q
      rw [← Nat.cast_mul, ← Nat.cast_add, h]
    have hAB : ((A - B : ℕ) : ℝ) = (A:ℝ) - (B:ℝ) := Nat.cast_sub hBA
    have hqa : (q:ℝ) * (((A/q:ℕ)):ℝ) = (A:ℝ) - ((A%q:ℕ):ℝ) := by linarith
    have hqb : (q:ℝ) * (((B/q:ℕ)):ℝ) = (B:ℝ) - ((B%q:ℕ):ℝ) := by linarith
    have key : (((A/q:ℕ)):ℝ) - (((B/q:ℕ)):ℝ) - ((A-B:ℕ):ℝ)/q
        = ((((B%q:ℕ)):ℝ) - (((A%q:ℕ)):ℝ))/(q:ℝ) := by
      rw [hAB]
      have hqa' : (((A/q:ℕ)):ℝ) * (q:ℝ) = (A:ℝ) - (((A%q:ℕ)):ℝ) := by
        rw [mul_comm]; exact hqa
      have hqb' : (((B/q:ℕ)):ℝ) * (q:ℝ) = (B:ℝ) - (((B%q:ℕ)):ℝ) := by
        rw [mul_comm]; exact hqb
      field_simp
      ring_nf
      linarith [hqa', hqb']
    rw [key, abs_div, abs_of_pos hqpos, div_le_one hqpos]
    have h1 : ((A%q:ℕ):ℝ) < (q:ℝ) := Nat.cast_lt.mpr (Nat.mod_lt A hq)
    have h2 : ((B%q:ℕ):ℝ) < (q:ℝ) := Nat.cast_lt.mpr (Nat.mod_lt B hq)
    have h3 : (0:ℝ) ≤ ((A%q:ℕ):ℝ) := Nat.cast_nonneg _
    have h4 : (0:ℝ) ≤ ((B%q:ℕ):ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  -- interval count
  have interval_card : ∀ lo hi r : ℕ, r < q →
      |(((Finset.Icc lo hi).filter (fun n => n % q = r)).card : ℝ) - ((Finset.Icc lo hi).card : ℝ)/q| ≤ 1 := by
    intro lo hi r hr
    by_cases hle : lo ≤ hi
    swap
    · have hempty : Finset.Icc lo hi = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty]
      simp
    have hunion : (Finset.range (hi+1)).filter (fun n => n % q = r)
        = (Finset.range lo).filter (fun n => n % q = r)
          ∪ (Finset.Ico lo (hi+1)).filter (fun n => n % q = r) := by
      rw [Finset.range_eq_Ico (hi+1), Finset.range_eq_Ico lo, ← Finset.filter_union,
        Finset.Ico_union_Ico_eq_Ico (by omega : 0 ≤ lo) (by omega : lo ≤ hi+1)]
    have hdisj : Disjoint ((Finset.range lo).filter (fun n => n % q = r))
        ((Finset.Ico lo (hi+1)).filter (fun n => n % q = r)) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hn1 hn2
      omega
    have hrec : ((Finset.range (hi+1)).filter (fun n => n % q = r)).card
        = ((Finset.range lo).filter (fun n => n % q = r)).card
          + ((Finset.Ico lo (hi+1)).filter (fun n => n % q = r)).card := by
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    rw [← Finset.Ico_add_one_right_eq_Icc]
    have hccard : ((Finset.Ico lo (hi+1)).filter (fun n => n % q = r)).card
        = (hi + q - r)/q - (lo + q - 1 - r)/q := by
      have h1 : ((Finset.range (hi+1)).filter (fun n => n % q = r)).card = (hi+1 + q - 1 - r)/q :=
        range_card (hi+1) r hr
      have h2 : ((Finset.range lo).filter (fun n => n % q = r)).card = (lo + q - 1 - r)/q :=
        range_card lo r hr
      have hA : hi + 1 + q - 1 - r = hi + q - r := by omega
      rw [hA] at h1
      have hrec' : (hi + q - r)/q = (lo + q - 1 - r)/q
          + ((Finset.Ico lo (hi+1)).filter (fun n => n % q = r)).card := by
        rw [← h1, ← h2]
        exact hrec
      omega
    rw [hccard, Nat.card_Ico]
    have hBA : lo + q - 1 - r ≤ hi + q - r := by omega
    have hdivle : (lo + q - 1 - r)/q ≤ (hi + q - r)/q := Nat.div_le_div_right hBA
    rw [Nat.cast_sub hdivle]
    have hAB : (hi + q - r) - (lo + q - 1 - r) = hi + 1 - lo := by omega
    have := div_diff (hi + q - r) (lo + q - 1 - r) hBA
    rwa [hAB] at this
  by_cases hwit : ∃ n : ℕ, q^100000 ≤ n^132301
  · have hTspec : q^100000 ≤ (Nat.find hwit)^132301 := Nat.find_spec hwit
    have hTmin : ∀ n : ℕ, q^100000 ≤ n^132301 → Nat.find hwit ≤ n := fun n hn => Nat.find_min' hwit hn
    have hiff : ∀ n : ℕ, (q^100000 ≤ n^132301) ↔ Nat.find hwit ≤ n := by
      intro n
      constructor
      · exact hTmin n
      · intro h
        exact le_trans hTspec (Nat.pow_le_pow_left h 132301)
    have hwin : window x q = Finset.Icc (max (x+1) (Nat.find hwit)) (2*x) := by
      ext n
      simp only [window, block, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, hiff n]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by omega, h2⟩, by omega⟩
    set W := Finset.Icc (max (x+1) (Nat.find hwit)) (2*x) with hWdef
    have hcount : countHits 1 x q = (W.filter (fun n => q ∣ n^2+1)).card := by
      simp [countHits, hwin]
    rw [hcount, hwin]
    have hfib : (W.filter (fun n => q ∣ n^2+1)).card
        = ∑ r ∈ roots 1 q, ((W.filter (fun n => q ∣ n^2+1)).filter (fun n => n % q = r)).card := by
      refine Finset.card_eq_sum_card_fiberwise ?_
      intro n hn
      obtain ⟨-, hnq⟩ := Finset.mem_filter.mp hn
      change n % q ∈ roots 1 q
      rw [memroots]
      refine ⟨?_, ?_⟩
      · rw [← ZMod.val_natCast q n]
        exact ZMod.val_lt (n : ZMod q)
      have h : ((n % q : ℕ) : ZMod q) = ((n : ZMod q)) := by
        rw [← ZMod.val_natCast q n]
        exact ZMod.natCast_zmod_val _
      have hq1 : ((n^2+1 : ℕ) : ZMod q) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact hnq
      have h2 : ((n : ZMod q))^2 + 1 = 0 := by
        rw [← hq1]; push_cast; ring
      have h3 : (((n % q : ℕ) : ZMod q))^2 + 1 = 0 := by rw [h]; exact h2
      have h4 : (((n % q)^2 + 1 : ℕ) : ZMod q) = 0 := by
        rw [← h3]; push_cast; ring
      exact (ZMod.natCast_eq_zero_iff _ _).1 h4
    have hfiber : ∀ r ∈ roots 1 q,
        ((W.filter (fun n => q ∣ n^2+1)).filter (fun n => n % q = r)).card
          = (W.filter (fun n => n % q = r)).card := by
      intro r hr
      congr 1
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro n hn
      constructor
      · rintro ⟨-, h2⟩; exact h2
      · intro h2
        refine ⟨?_, h2⟩
        have hcongr : n ≡ r [MOD q] := by
          show n % q = r % q
          rw [h2, Nat.mod_eq_of_lt ((memroots r).1 hr).1]
        have hmod : (n^2+1) % q = (r^2+1) % q :=
          Nat.ModEq.add (Nat.ModEq.pow 2 hcongr) (Nat.ModEq.refl 1)
        rw [Nat.dvd_iff_mod_eq_zero, hmod, ← Nat.dvd_iff_mod_eq_zero]
        exact (memroots r).1 hr |>.2
    have hfib2 : (W.filter (fun n => q ∣ n^2+1)).card
        = ∑ r ∈ roots 1 q, (W.filter (fun n => n % q = r)).card := by
      rw [hfib]
      apply Finset.sum_congr rfl
      intro r hr
      exact hfiber r hr
    have hper : ∀ r ∈ roots 1 q,
        |((W.filter (fun n => n % q = r)).card : ℝ) - (W.card : ℝ)/q| ≤ 1 := by
      intro r hr
      exact interval_card _ _ r ((memroots r).1 hr).1
    have hconst : ∑ r ∈ roots 1 q, ((W.card : ℝ)/q) = (W.card : ℝ) * ((roots 1 q).card : ℝ)/q := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    have hgoal : |(∑ r ∈ roots 1 q, ((W.filter (fun n => n % q = r)).card : ℝ)) - (W.card:ℝ)*((roots 1 q).card:ℝ)/q| ≤ ((roots 1 q).card : ℝ) := by
      rw [← hconst, ← Finset.sum_sub_distrib]
      calc |∑ r ∈ roots 1 q, (((W.filter (fun n => n % q = r)).card : ℝ) - (W.card : ℝ)/q)|
          ≤ ∑ r ∈ roots 1 q, |((W.filter (fun n => n % q = r)).card : ℝ) - (W.card : ℝ)/q| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ roots 1 q, (1:ℝ) := Finset.sum_le_sum hper
        _ = ((roots 1 q).card : ℝ) := by simp
    rw [hfib2]
    simpa only [Nat.cast_sum] using hgoal
  · have hwin : window x q = ∅ := by
      simp only [window]
      apply Finset.filter_eq_empty_iff.mpr
      intro n hn hP
      exact hwit ⟨n, hP⟩
    have hz : countHits 1 x q = 0 := by simp [countHits, hwin]
    rw [hz, hwin]
    simp
