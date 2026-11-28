import Mathlib

open Finset

namespace MertensGridUpper

private abbrev D : ℕ := 10^22
private abbrev K : ℕ := 1073741824
private def up (a b : ℕ) := a / b + 1

private theorem up_ge (a b : ℕ) (hb : 0 < b) : (a:ℝ)/b ≤ (up a b : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hb)).2
  exact_mod_cast (Nat.lt_mul_of_div_lt (Nat.lt_succ_self (a/b)) hb).le

private def sq : ℕ → ℕ → ℕ
  | 0, a => a
  | k+1, a => let b := sq k a; up (b*b) D
private def ex (a : ℕ) := sq 30 (up (D*D*K) (D*K-a))

private theorem sq_ge (k a : ℕ) (t : ℝ) (h : Real.exp t ≤ (a:ℝ)/D) :
    Real.exp ((2:ℝ)^k*t) ≤ (sq k a : ℝ)/D := by
  induction k with
  | zero => simpa [sq] using h
  | succ k ih =>
    rw [show (2:ℝ)^(k+1)*t=2^k*t+2^k*t by ring, Real.exp_add]
    apply (mul_self_le_mul_self (Real.exp_pos _).le ih).trans
    have hh := up_ge (sq k a * sq k a) D (by decide)
    push_cast at hh
    change _ ≤ (up (sq k a * sq k a) D : ℝ)/D
    norm_num [D] at hh ⊢
    linarith

private theorem ex_ge (a : ℕ) (ha : a < D*K) : Real.exp ((a:ℝ)/D) ≤ (ex a : ℝ)/D := by
  have hpos : 0 < D*K-a := by omega
  have hk : (a:ℝ) < (D:ℝ)*K := by exact_mod_cast ha
  have hh := up_ge (D*D*K) (D*K-a) hpos
  rw [Nat.cast_sub ha.le] at hh
  push_cast at hh
  have hfrac : (a:ℝ)/D/K < 1 := by
    apply (div_lt_iff₀ (by norm_num [K])).mpr
    apply (div_lt_iff₀ (by norm_num [D])).mpr
    simpa [mul_comm] using hk
  have ht := Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ (a:ℝ)/D/K) hfrac
  have h1 : Real.exp ((a:ℝ)/D/K) ≤ (up (D*D*K) (D*K-a) : ℝ)/D := by
    refine ht.trans ?_
    calc 1/(1-(a:ℝ)/D/K) = (((D:ℝ)*D*K)/((D:ℝ)*K-a))/D := by
           field_simp
           <;> ring
         _ ≤ _ := div_le_div_of_nonneg_right (by norm_num [D,K] at hh ⊢; exact hh) (by norm_num [D])
  have h2 := sq_ge 30 _ _ h1
  convert h2 using 2 <;> norm_num [K,ex] <;> ring

private noncomputable def S (i : ℕ) : ℝ := ∑ p ∈ (range i).filter Nat.Prime, (1:ℝ)/p
private theorem S_succ (i : ℕ) :
    S (i+1) = S i + if Nat.Prime i then (1:ℝ)/i else 0 := by
  simp [S,sum_filter,sum_range_succ]
private theorem S_mono : Monotone S := by
  apply monotone_nat_of_le_succ
  intro i
  rw [S_succ]
  apply le_add_of_nonneg_right; split <;> positivity
-- Bounded primality criterion adapted from the accepted lower-grid proof, commit
-- ed0b2428d69a876757ab067a438fcf6afce8e743.
def primorial : ℕ := 10014646650599190067509233131649940057366334653200433090

theorem primorial_eq : primorial = ∏ p ∈ (range 149).filter Nat.Prime, p := by
  decide +kernel

def fastPrime (n : ℕ) : Bool :=
  if n ≤ 148 then decide (Nat.Prime n) else decide (n.Coprime primorial)

private theorem coprime_of_prime {n : ℕ} (hn : 148 < n) (hp : Nat.Prime n) :
    n.Coprime primorial := by
  rw [primorial_eq, Nat.coprime_prod_right_iff]
  intro p hMem
  obtain ⟨hRange, hPrime⟩ := mem_filter.mp hMem
  have hp149 : p < 149 := mem_range.mp hRange
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hPrime.pos (by omega))

/-- The bounded least-factor argument follows the accepted Taskdc0a505371b58c19da53c009. -/
private theorem prime_of_coprime {n : ℕ} (hn : 148 < n) (hN : n ≤ 22144)
    (hc : n.Coprime primorial) : Nat.Prime n := by
  by_contra hNot
  have hPrime := Nat.minFac_prime (show n ≠ 1 by omega)
  have hSquare := Nat.minFac_sq_le_self (show 0 < n by omega) hNot
  have hSmall : n.minFac < 149 := by
    by_contra! hLarge
    have h := Nat.pow_le_pow_left hLarge 2
    norm_num at h
    omega
  have hFactor : n.minFac ∣ primorial := by
    rw [primorial_eq]
    exact dvd_prod_of_mem (fun p : ℕ => p) (mem_filter.mpr ⟨mem_range.mpr hSmall, hPrime⟩)
  have hGcd := Nat.dvd_gcd (Nat.minFac_dvd n) hFactor
  rw [Nat.coprime_iff_gcd_eq_one.mp hc] at hGcd
  exact hPrime.not_dvd_one hGcd

theorem fastPrime_spec {n : ℕ} (hN : n ≤ 22144) : fastPrime n = true ↔ Nat.Prime n := by
  by_cases h : n ≤ 148
  · rw [fastPrime, ite_eq_left h, decide_eq_true_eq]
  · rw [fastPrime, ite_eq_right h, decide_eq_true_eq]
    have hn : 148 < n := Nat.lt_of_not_ge h
    exact ⟨prime_of_coprime hn hN, coprime_of_prime hn⟩


private def primeTest (n : ℕ) : Bool := if n ≤ 22144 then fastPrime n else decide (Nat.Prime n)
private theorem primeTest_spec (n : ℕ) : primeTest n = true ↔ Nat.Prime n := by
  by_cases hn : n ≤ 22144
  · simpa [primeTest, hn] using fastPrime_spec hn
  · simp [primeTest, hn]
private def gain (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => gain i k + if primeTest (i+k) then up D (i+k) else 0
private theorem gain_ge (i k : ℕ) : S (i+k)-S i ≤ (gain i k : ℝ)/D := by
  induction k with
  | zero => simp [gain]
  | succ k ih =>
    rw [← Nat.add_assoc,S_succ]
    simp only [gain,Nat.cast_add,add_div]
    simp only [primeTest_spec]
    split_ifs with h
    · have hu := up_ge D (i+k) h.pos
      push_cast at hu
      norm_num [D,div_eq_mul_inv] at hu ih ⊢
      linarith
    · simp_all

private def Block (c i j s t : ℕ) : Prop := S i ≤ (s:ℝ)/D → S j ≤ (t:ℝ)/D ∧
  ∀ x : ℕ, i < x → x ≤ j → S x ≤ Real.log (Real.log ((max 2 (x-1):ℕ):ℝ)) + (c:ℝ)/D

private theorem segment (c i j s t : ℕ) (hij : i ≤ j) (hi : 2 ≤ i)
    (ht : s+gain i (j-i) ≤ t) (h1 : t-c < D*K) (h2 : ex (t-c) < D*K)
    (h3 : ex (ex (t-c)) ≤ i*D) : Block c i j s t := by
  intro hs
  have hg := gain_ge i (j-i)
  rw [Nat.add_sub_of_le hij] at hg
  have hh : (s:ℝ)+(gain i (j-i):ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hj : S j ≤ (t:ℝ)/D := by norm_num [D] at hs hg ⊢; linarith
  refine ⟨hj,?_⟩
  intro x hx hxj
  have hsub : (t:ℝ)/D-(c:ℝ)/D ≤ ((t-c:ℕ):ℝ)/D := by
    by_cases h : c≤t
    · rw [Nat.cast_sub h]; ring_nf; rfl
    · rw [Nat.sub_eq_zero_of_le (by omega)]; push_cast; have h' : (t:ℝ) ≤ c := by exact_mod_cast (show t≤c by omega)
      norm_num [D]; linarith
  have h4 := (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hsub)).trans
    ((Real.exp_le_exp.mpr (ex_ge _ h1)).trans (ex_ge _ h2))
  have h5 : ((ex (ex (t-c))):ℝ) ≤ (i:ℝ)*D := by exact_mod_cast h3
  have lb : i ≤ max 2 (x-1) := by omega
  have hp : 0 < Real.log ((max 2 (x-1):ℕ):ℝ) := Real.log_pos (by exact_mod_cast (show 1 < max 2 (x-1) by omega))
  have h6 : Real.exp (Real.exp ((t:ℝ)/D-(c:ℝ)/D)) ≤ ((max 2 (x-1):ℕ):ℝ) := by
    apply h4.trans
    apply le_trans _ (Nat.cast_le.mpr lb)
    exact (div_le_iff₀ (by norm_num [D])).mpr h5
  have h7 := (Real.le_log_iff_exp_le (by positivity : (0:ℝ)<((max 2 (x-1):ℕ):ℝ))).mpr h6
  have h8 := (Real.le_log_iff_exp_le hp).mpr h7
  linarith [S_mono hxj]
private theorem join {c i j k s t u : ℕ} (a : Block c i j s t) (b : Block c j k t u) :
    Block c i k s u := by
  intro hs
  obtain ⟨ht,ha⟩ := a hs
  obtain ⟨hu,hb⟩ := b ht
  refine ⟨hu,fun x hi hk => ?_⟩
  by_cases h : x ≤ j
  · exact ha x hi h
  · exact hb x (by omega) hk



private theorem start_S : S 3 ≤ (5000000000000000000000:ℝ)/D := by
  norm_num [S,D,Finset.sum_filter,Finset.sum_range_succ]

private theorem log_cut : Real.log (7200:ℝ) ≤ 8.9 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  apply le_of_pow_le_pow_left₀ (n := 10) (by decide) (Real.exp_pos _).le
  rw [← Real.exp_nat_mul]
  norm_num1
  have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (2.7182818283:ℝ)) Real.exp_one_gt_d9.le 89
  rw [← Real.exp_nat_mul] at h
  norm_num1 at h
  exact le_trans (by norm_num) h
private theorem b3 : Block 12614970000000000000000 3 17 5000000000000000000000 13440226440226440226444 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17 : Block 12614970000000000000000 17 145 13440226440226440226444 18797977110648115591851 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b145 : Block 12614970000000000000000 145 273 18797977110648115591851 19987400431470443580043 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b273 : Block 12614970000000000000000 273 401 19987400431470443580043 20587765264224639184330 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b401 : Block 12614970000000000000000 401 529 20587765264224639184330 21044936926371312603697 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b529 : Block 12614970000000000000000 529 657 21044936926371312603697 21379990211254000644901 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b657 : Block 12614970000000000000000 657 785 21379990211254000644901 21631309390794561136810 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b785 : Block 12614970000000000000000 785 913 21631309390794561136810 21855634238659123026139 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b913 : Block 12614970000000000000000 913 1041 21855634238659123026139 22049196107055484121062 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1041 : Block 12614970000000000000000 1041 1169 22049196107055484121062 22203818683777570761735 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1169 : Block 12614970000000000000000 1169 1297 22203818683777570761735 22349837626952061985258 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1297 : Block 12614970000000000000000 1297 1425 22349837626952061985258 22453707027768375439189 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1425 : Block 12614970000000000000000 1425 1553 22453707027768375439189 22588934988278769424070 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1553 : Block 12614970000000000000000 1553 1681 22588934988278769424070 22706970366969245440929 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1681 : Block 12614970000000000000000 1681 1809 22706970366969245440929 22798723352283233071765 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1809 : Block 12614970000000000000000 1809 1937 22798723352283233071765 22884046739300084359001 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1937 : Block 12614970000000000000000 1937 2065 22884046739300084359001 22963892470117951147276 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2065 : Block 12614970000000000000000 2065 2193 22963892470117951147276 23039411922867175838382 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2193 : Block 12614970000000000000000 2193 2321 23039411922867175838382 23114687803657079118165 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2321 : Block 12614970000000000000000 2321 2449 23114687803657079118165 23194330976321320631769 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2449 : Block 12614970000000000000000 2449 2577 23194330976321320631769 23242069776195165338629 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2577 : Block 12614970000000000000000 2577 2705 23242069776195165338629 23310053617529352627714 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2705 : Block 12614970000000000000000 2705 2833 23310053617529352627714 23371688464634447864689 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2833 : Block 12614970000000000000000 2833 2961 23371688464634447864689 23427050306186377385657 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2961 : Block 12614970000000000000000 2961 3089 23427050306186377385657 23476647123912264631067 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3089 : Block 12614970000000000000000 3089 3217 23476647123912264631067 23517827124461189813677 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3217 : Block 12614970000000000000000 3217 3345 23517827124461189813677 23569605661685777481788 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3345 : Block 12614970000000000000000 3345 3473 23569605661685777481788 23616490802688195787116 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3473 : Block 12614970000000000000000 3473 3601 23616490802688195787116 23661661321736224862553 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3601 : Block 12614970000000000000000 3601 3729 23661661321736224862553 23708058471646538664887 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3729 : Block 12614970000000000000000 3729 3857 23708058471646538664887 23747557638612810577413 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3857 : Block 12614970000000000000000 3857 3985 23747557638612810577413 23783323304547102461821 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3985 : Block 12614970000000000000000 3985 4113 23783323304547102461821 23825343221710961656115 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4113 : Block 12614970000000000000000 4113 4241 23825343221710961656115 23858860576511878011564 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4241 : Block 12614970000000000000000 4241 4369 23858860576511878011564 23896104689558900867508 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4369 : Block 12614970000000000000000 4369 4497 23896104689558900867508 23927653464710003036299 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4497 : Block 12614970000000000000000 4497 4625 23927653464710003036299 23958377389825816503630 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4625 : Block 12614970000000000000000 4625 4753 23958377389825816503630 23992539252383827305375 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4753 : Block 12614970000000000000000 4753 4881 23992539252383827305375 24019545673815143278238 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4881 : Block 12614970000000000000000 4881 5009 24019545673815143278238 24053885377625321811663 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5009 : Block 12614970000000000000000 5009 5137 24053885377625321811663 24083493422759821368692 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5137 : Block 12614970000000000000000 5137 5265 24083493422759821368692 24108494152626562609493 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5265 : Block 12614970000000000000000 5265 5393 24108494152626562609493 24131043150820740939195 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5393 : Block 12614970000000000000000 5393 5521 24131043150820740939195 24165894150163932795876 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5521 : Block 12614970000000000000000 5521 5649 24165894150163932795876 24189185594590887668343 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5649 : Block 12614970000000000000000 5649 5777 24189185594590887668343 24215516783490971464344 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5777 : Block 12614970000000000000000 5777 5905 24215516783490971464344 24249759395473992209772 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5905 : Block 12614970000000000000000 5905 6033 24249759395473992209772 24264827771611114835892 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6033 : Block 12614970000000000000000 6033 6161 24264827771611114835892 24291092643374112271484 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6161 : Block 12614970000000000000000 6161 6289 24291092643374112271484 24316774702045754303629 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6289 : Block 12614970000000000000000 6289 6417 24316774702045754303629 24341987499748097385512 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6417 : Block 12614970000000000000000 6417 6545 24341987499748097385512 24357441015115651319098 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6545 : Block 12614970000000000000000 6545 6673 24357441015115651319098 24380181263688963530851 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6673 : Block 12614970000000000000000 6673 6801 24380181263688963530851 24403951403088799783138 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6801 : Block 12614970000000000000000 6801 6929 24403951403088799783138 24425810839455003272896 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6929 : Block 12614970000000000000000 6929 7057 24425810839455003272896 24448700289202811727921 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7057 : Block 12614970000000000000000 7057 7185 24448700289202811727921 24464157823655523709042 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7185 : Block 12614970000000000000000 7185 7200 24464157823655523709042 24466939465308081152893 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem early : Block 12614970000000000000000 3 7200 5000000000000000000000 24466939465308081152893 := (join (join (join (join (join (join b3 b17) (join b145 b273)) (join (join b401 b529) (join b657 b785))) (join (join (join b913 b1041) (join b1169 b1297)) (join (join b1425 b1553) (join b1681 b1809)))) (join (join (join (join b1937 b2065) (join b2193 b2321)) (join (join b2449 b2577) (join b2705 b2833))) (join (join (join b2961 b3089) (join b3217 b3345)) (join (join b3473 b3601) (join b3729 b3857))))) (join (join (join (join (join b3985 b4113) (join b4241 b4369)) (join (join b4497 b4625) (join b4753 b4881))) (join (join (join b5009 b5137) (join b5265 b5393)) (join (join b5521 b5649) (join b5777 b5905)))) (join (join (join (join b6033 b6161) (join b6289 b6417)) (join (join b6545 b6673) (join b6801 b6929))) (join b7057 b7185))))
private theorem b7200 : Block 2631110000000000000000 7200 7219 24466939465308081152893 24471100161104528537202 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7219 : Block 2631110000000000000000 7219 7237 24471100161104528537202 24473868711710991159825 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7237 : Block 2631110000000000000000 7237 7247 24473868711710991159825 24476631143124521781636 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7247 : Block 2631110000000000000000 7247 7253 24476631143124521781636 24478011024454727383955 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7253 : Block 2631110000000000000000 7253 7283 24478011024454727383955 24479389764286521124477 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7283 : Block 2631110000000000000000 7283 7309 24479389764286521124477 24483501801745844072081 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7309 : Block 2631110000000000000000 7309 7333 24483501801745844072081 24487599981968599549222 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7333 : Block 2631110000000000000000 7333 7369 24487599981968599549222 24491684768804268235679 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7369 : Block 2631110000000000000000 7369 7433 24491684768804268235679 24497092035482627532994 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7433 : Block 2631110000000000000000 7433 7489 24497092035482627532994 24506470976116523669302 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7489 : Block 2631110000000000000000 7489 7537 24506470976116523669302 24514459641589043649147 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7537 : Block 2631110000000000000000 7537 7573 24514459641589043649147 24522407724779757676111 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7573 : Block 2631110000000000000000 7573 7591 24522407724779757676111 24527684424941683721324 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7591 : Block 2631110000000000000000 7591 7607 24527684424941683721324 24530317044722548359671 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7607 : Block 2631110000000000000000 7607 7621 24530317044722548359671 24531631623400082210072 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7621 : Block 2631110000000000000000 7621 7643 24531631623400082210072 24534252859026164768792 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7643 : Block 2631110000000000000000 7643 7673 24534252859026164768792 24538172557196007347759 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7673 : Block 2631110000000000000000 7673 7691 24538172557196007347759 24542078639839409218285 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7691 : Block 2631110000000000000000 7691 7703 24542078639839409218285 24544677730860100296491 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7703 : Block 2631110000000000000000 7703 7717 24544677730860100296491 24545975926368343837969 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7717 : Block 2631110000000000000000 7717 7727 24545975926368343837969 24548566600334693030182 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7727 : Block 2631110000000000000000 7727 7741 24548566600334693030182 24549860763658104444703 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7741 : Block 2631110000000000000000 7741 7753 24549860763658104444703 24551152586420021509682 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7753 : Block 2631110000000000000000 7753 7759 24551152586420021509682 24553731567893938853344 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7759 : Block 2631110000000000000000 7759 7789 24553731567893938853344 24555020393773562516188 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7789 : Block 2631110000000000000000 7789 7823 24555020393773562516188 24558866721648830008242 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7823 : Block 2631110000000000000000 7823 7867 24558866721648830008242 24563971052208635910729 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7867 : Block 2631110000000000000000 7867 7901 24563971052208635910729 24570319616671313287139 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7901 : Block 2631110000000000000000 7901 7927 24570319616671313287139 24574112767113577477890 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7927 : Block 2631110000000000000000 7927 7949 24574112767113577477890 24577894757455214158056 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7949 : Block 2631110000000000000000 7949 7993 24577894757455214158056 24581666288877978990559 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7993 : Block 2631110000000000000000 7993 8053 24581666288877978990559 24587905547721612150721 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8053 : Block 2631110000000000000000 8053 8093 24587905547721612150721 24595337750514049004270 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8093 : Block 2631110000000000000000 8093 8147 24595337750514049004270 24601503749877572748550 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8147 : Block 2631110000000000000000 8147 8209 24601503749877572748550 24608848311334690708903 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8209 : Block 2631110000000000000000 8209 8263 24608848311334690708903 24617356304638091630541 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8263 : Block 2631110000000000000000 8263 8297 24617356304638091630541 24624603278957312202421 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8297 : Block 2631110000000000000000 8297 8353 24624603278957312202421 24629414739454388640260 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8353 : Block 2631110000000000000000 8353 8419 24629414739454388640260 24636580646583730627944 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8419 : Block 2631110000000000000000 8419 8467 24636580646583730627944 24644878299607483976995 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8467 : Block 2631110000000000000000 8467 8539 24644878299607483976995 24651928049945894869854 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8539 : Block 2631110000000000000000 8539 8623 24651928049945894869854 24661257026910008038812 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8623 : Block 2631110000000000000000 8623 8689 24661257026910008038812 24671660777553138351293 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8689 : Block 2631110000000000000000 8689 8737 24671660777553138351293 24679700042472241848292 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8737 : Block 2631110000000000000000 8737 8783 24679700042472241848292 24686554852630588018932 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8783 : Block 2631110000000000000000 8783 8831 24686554852630588018932 24692232426290103436926 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8831 : Block 2631110000000000000000 8831 8863 24692232426290103436926 24697886368319602235426 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8863 : Block 2631110000000000000000 8863 8923 24697886368319602235426 24702392150645545435688 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8923 : Block 2631110000000000000000 8923 8969 24702392150645545435688 24709103575565737136314 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8969 : Block 2631110000000000000000 8969 9011 24709103575565737136314 24714665699831884180556 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9011 : Block 2631110000000000000000 9011 9049 24714665699831884180556 24720204405476494359072 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9049 : Block 2631110000000000000000 9049 9103 24720204405476494359072 24724616264190681690827 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9103 : Block 2631110000000000000000 9103 9157 24724616264190681690827 24731190427100162907776 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9157 : Block 2631110000000000000000 9157 9203 24731190427100162907776 24737729002862084303926 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9203 : Block 2631110000000000000000 9203 9241 24737729002862084303926 24743152124463545613861 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9241 : Block 2631110000000000000000 9241 9283 24743152124463545613861 24747469926793408731465 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9283 : Block 2631110000000000000000 9283 9337 24747469926793408731465 24752842934641691671906 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9337 : Block 2631110000000000000000 9337 9391 24752842934641691671906 24759258005925000399748 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9391 : Block 2631110000000000000000 9391 9431 24759258005925000399748 24765636017879637174943 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9431 : Block 2631110000000000000000 9431 9461 24765636017879637174943 24769875552007184825354 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9461 : Block 2631110000000000000000 9461 9473 24769875552007184825354 24773045570895286475083 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9473 : Block 2631110000000000000000 9473 9491 24773045570895286475083 24775156166294671829880 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9491 : Block 2631110000000000000000 9491 9511 24775156166294671829880 24777262760143100494260 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9511 : Block 2631110000000000000000 9511 9533 24777262760143100494260 24779364484136538194594 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9533 : Block 2631110000000000000000 9533 9547 24779364484136538194594 24781461799780354219500 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9547 : Block 2631110000000000000000 9547 9587 24781461799780354219500 24783556260025128824685 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9587 : Block 2631110000000000000000 9587 9623 24783556260025128824685 24787720764456817461435 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9623 : Block 2631110000000000000000 9623 9649 24787720764456817461435 24791873806323142276102 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9649 : Block 2631110000000000000000 9649 9679 24791873806323142276102 24794978650798052797254 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9679 : Block 2631110000000000000000 9679 9719 24794978650798052797254 24798075160414278656512 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9719 : Block 2631110000000000000000 9719 9749 24798075160414278656512 24803213383429509857497 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9749 : Block 2631110000000000000000 9749 9781 24803213383429509857497 24806286631728853684626 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9781 : Block 2631110000000000000000 9781 9803 24806286631728853684626 24809352131775604986469 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9803 : Block 2631110000000000000000 9803 9829 24809352131775604986469 24812410132888673555923 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9829 : Block 2631110000000000000000 9829 9851 24812410132888673555923 24815460877464009606665 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9851 : Block 2631110000000000000000 9851 9859 24815460877464009606665 24817490510288622358789 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9859 : Block 2631110000000000000000 9859 9871 24817490510288622358789 24818504811941934053688 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9871 : Block 2631110000000000000000 9871 9883 24818504811941934053688 24819517880526677240802 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9883 : Block 2631110000000000000000 9883 9901 24819517880526677240802 24821541148186639038603 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9901 : Block 2631110000000000000000 9901 9923 24821541148186639038603 24823560534478547790603 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9923 : Block 2631110000000000000000 9923 9931 24823560534478547790603 24825575444999093711995 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9931 : Block 2631110000000000000000 9931 9941 24825575444999093711995 24826582392939885173077 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9941 : Block 2631110000000000000000 9941 9949 24826582392939885173077 24827588327956483100851 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9949 : Block 2631110000000000000000 9949 9967 24827588327956483100851 24828593454099814088890 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9967 : Block 2631110000000000000000 9967 10007 24828593454099814088890 24830599472335606361618 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10007 : Block 2631110000000000000000 10007 10061 24830599472335606361618 24834590302424980427643 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10061 : Block 2631110000000000000000 10061 10099 24834590302424980427643 24840544660961461223305 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10099 : Block 2631110000000000000000 10099 10139 24840544660961461223305 24844500559444712783783 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10139 : Block 2631110000000000000000 10139 10163 24844500559444712783783 24848442419523164766036 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10163 : Block 2631110000000000000000 10163 10181 24848442419523164766036 24851392369656495731460 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10181 : Block 2631110000000000000000 10181 10211 24851392369656495731460 24853355656879239590038 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10211 : Block 2631110000000000000000 10211 10247 24853355656879239590038 24856289455813260154445 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10247 : Block 2631110000000000000000 10247 10271 24856289455813260154445 24860189423718082601572 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10271 : Block 2631110000000000000000 10271 10301 24860189423718082601572 24863108375985390946088 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10301 : Block 2631110000000000000000 10301 10321 24863108375985390946088 24866019396567697873901 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10321 : Block 2631110000000000000000 10321 10333 24866019396567697873901 24867956255437470946951 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10333 : Block 2631110000000000000000 10333 10337 24867956255437470946951 24868924028591443655749 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10337 : Block 2631110000000000000000 10337 10343 24868924028591443655749 24869891427256433498064 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10343 : Block 2631110000000000000000 10343 10357 24869891427256433498064 24870858264731054014356 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10357 : Block 2631110000000000000000 10357 10369 24870858264731054014356 24871823795290096208042 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10369 : Block 2631110000000000000000 10369 10391 24871823795290096208042 24872788208444691636724 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10391 : Block 2631110000000000000000 10391 10429 24872788208444691636724 24875671259277348363435 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10429 : Block 2631110000000000000000 10429 10459 24875671259277348363435 24879501581434199367328 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10459 : Block 2631110000000000000000 10459 10487 24879501581434199367328 24882367916314597561756 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10487 : Block 2631110000000000000000 10487 10513 24882367916314597561756 24885226239789034425952 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10513 : Block 2631110000000000000000 10513 10559 24885226239789034425952 24888076778310971755990 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10559 : Block 2631110000000000000000 10559 10607 24888076778310971755990 24892801526853864954991 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10607 : Block 2631110000000000000000 10607 10651 24892801526853864954991 24897508123730234283528 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10651 : Block 2631110000000000000000 10651 10691 24897508123730234283528 24902196362460068882661 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10691 : Block 2631110000000000000000 10691 10729 24902196362460068882661 24905931717143465188192 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10729 : Block 2631110000000000000000 10729 10771 24905931717143465188192 24909656634840310811814 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10771 : Block 2631110000000000000000 10771 10837 24909656634840310811814 24914288768893756844124 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10837 : Block 2631110000000000000000 10837 10889 24914288768893756844124 24920735553706544048159 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10889 : Block 2631110000000000000000 10889 10949 24920735553706544048159 24926234441932721350904 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10949 : Block 2631110000000000000000 10949 11003 24926234441932721350904 24931702419845869951651 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11003 : Block 2631110000000000000000 11003 11071 24931702419845869951651 24937135420310301421304 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11071 : Block 2631110000000000000000 11071 11131 24937135420310301421304 24943443122231498223981 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11131 : Block 2631110000000000000000 11131 11197 24943443122231498223981 24949715454485788769693 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11197 : Block 2631110000000000000000 11197 11273 24949715454485788769693 24955944740670268916253 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11273 : Block 2631110000000000000000 11273 11351 24955944740670268916253 24963023154661282975314 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11351 : Block 2631110000000000000000 11351 11443 24963023154661282975314 24970924177823478293459 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11443 : Block 2631110000000000000000 11443 11527 24970924177823478293459 24979634255196447838869 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11527 : Block 2631110000000000000000 11527 11633 24979634255196447838869 24987406253998552132095 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11633 : Block 2631110000000000000000 11633 11761 24987406253998552132095 24996811902773275880837 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11761 : Block 2631110000000000000000 11761 11887 24996811902773275880837 25008659881027494294965 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11887 : Block 2631110000000000000000 11887 11981 25008659881027494294965 25019555356799972582829 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11981 : Block 2631110000000000000000 11981 12101 25019555356799972582829 25028694613837006757991 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12101 : Block 2631110000000000000000 12101 12211 25028694613837006757991 25038576517040470209271 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12211 : Block 2631110000000000000000 12211 12323 25038576517040470209271 25048365684966846239318 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12323 : Block 2631110000000000000000 12323 12433 25048365684966846239318 25058062327805383114362 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12433 : Block 2631110000000000000000 12433 12527 25058062327805383114362 25067679298650479339225 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12527 : Block 2631110000000000000000 12527 12611 25067679298650479339225 25075639461837314710852 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12611 : Block 2631110000000000000000 12611 12689 25075639461837314710852 25082760295951853064348 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12689 : Block 2631110000000000000000 12689 12763 25082760295951853064348 25089049500372077911616 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12763 : Block 2631110000000000000000 12763 12841 25089049500372077911616 25095298541476076553559 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12841 : Block 2631110000000000000000 12841 12919 25095298541476076553559 25101505529743551066626 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12919 : Block 2631110000000000000000 12919 13001 25101505529743551066626 25108452555324107843054 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13001 : Block 2631110000000000000000 13001 13063 25108452555324107843054 25114595663317558123079 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13063 : Block 2631110000000000000000 13063 13147 25114595663317558123079 25119938312617079146646 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13147 : Block 2631110000000000000000 13147 13219 25119938312617079146646 25126770600758907050861 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13219 : Block 2631110000000000000000 13219 13309 25126770600758907050861 25132805399347658817601 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13309 : Block 2631110000000000000000 13309 13399 25132805399347658817601 25139549754071663887054 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13399 : Block 2631110000000000000000 13399 13487 25139549754071663887054 25146989925133494266848 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13487 : Block 2631110000000000000000 13487 13597 25146989925133494266848 25153637648013679317712 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13597 : Block 2631110000000000000000 13597 13697 25153637648013679317712 25162426868520100331686 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13697 : Block 2631110000000000000000 13697 13781 25162426868520100331686 25169709148558315155063 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13781 : Block 2631110000000000000000 13781 13877 25169709148558315155063 25176219961708837533476 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13877 : Block 2631110000000000000000 13877 13963 25176219961708837533476 25183411736768257152054 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13963 : Block 2631110000000000000000 13963 14057 25183411736768257152054 25189837324207453854241 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14057 : Block 2631110000000000000000 14057 14173 25189837324207453854241 25196925046036720907511 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14173 : Block 2631110000000000000000 14173 14301 25196925046036720907511 25203952901086359883936 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14301 : Block 2631110000000000000000 14301 14429 25203952901086359883936 25213696076176532471431 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14429 : Block 2631110000000000000000 14429 14557 25213696076176532471431 25223354758163664246072 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14557 : Block 2631110000000000000000 14557 14685 25223354758163664246072 25232930938371729824005 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14685 : Block 2631110000000000000000 14685 14797 25232930938371729824005 25242426169474640582452 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14797 : Block 2631110000000000000000 14797 14897 25242426169474640582452 25250508097961428750457 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14897 : Block 2631110000000000000000 14897 15025 25250508097961428750457 25257862643843213576226 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15025 : Block 2631110000000000000000 15025 15149 25257862643843213576226 25266476123925588711923 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15149 : Block 2631110000000000000000 15149 15271 25266476123925588711923 25275021414053294937724 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15271 : Block 2631110000000000000000 15271 15373 25275021414053294937724 25283510024817947545262 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15373 : Block 2631110000000000000000 15373 15467 25283510024817947545262 25290646210996611386544 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15467 : Block 2631110000000000000000 15467 15569 25290646210996611386544 25296447737538455829591 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15569 : Block 2631110000000000000000 15569 15661 25296447737538455829591 25303492104067321349034 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15661 : Block 2631110000000000000000 15661 15749 25303492104067321349034 25309860420313079567568 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15749 : Block 2631110000000000000000 15749 15817 25309860420313079567568 25315563168231735196436 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15817 : Block 2631110000000000000000 15817 15901 25315563168231735196436 25319976284427751830394 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15901 : Block 2631110000000000000000 15901 15991 25319976284427751830394 25325624716963865084388 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15991 : Block 2631110000000000000000 15991 16073 25325624716963865084388 25331236136217739980294 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16073 : Block 2631110000000000000000 16073 16141 25331236136217739980294 25336204008173709048601 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16141 : Block 2631110000000000000000 16141 16231 25336204008173709048601 25341143741320735316681 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16231 : Block 2631110000000000000000 16231 16349 25341143741320735316681 25346670328057293153575 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16349 : Block 2631110000000000000000 16349 16453 25346670328057293153575 25353986318218057365677 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16453 : Block 2631110000000000000000 16453 16573 25353986318218057365677 25360646890231524704780 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16573 : Block 2631110000000000000000 16573 16693 25360646890231524704780 25367859610765013966787 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16693 : Block 2631110000000000000000 16693 16821 25367859610765013966787 25373832213382561234042 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16821 : Block 2631110000000000000000 16821 16949 25373832213382561234042 25382714624518215789111 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16949 : Block 2631110000000000000000 16949 17077 25382714624518215789111 25390355999012210337443 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17077 : Block 2631110000000000000000 17077 17205 25390355999012210337443 25397939788517545826992 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17205 : Block 2631110000000000000000 17205 17333 25397939788517545826992 25404308550418750391724 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17333 : Block 2631110000000000000000 17333 17461 25404308550418750391724 25412933471069199884209 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17461 : Block 2631110000000000000000 17461 17589 25412933471069199884209 25421495323540926525991 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17589 : Block 2631110000000000000000 17589 17717 25421495323540926525991 25428293452907220462747 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17717 : Block 2631110000000000000000 17717 17845 25428293452907220462747 25435041500244393207166 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17845 : Block 2631110000000000000000 17845 17973 25435041500244393207166 25442856271591311440812 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17973 : Block 2631110000000000000000 17973 18101 25442856271591311440812 25450618376858860917767 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18101 : Block 2631110000000000000000 18101 18229 25450618376858860917767 25458325415918995145823 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18229 : Block 2631110000000000000000 18229 18341 25458325415918995145823 25465437363409297818385 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18341 : Block 2631110000000000000000 18341 18451 25465437363409297818385 25471960187438272238382 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18451 : Block 2631110000000000000000 18451 18553 25471960187438272238382 25477906530054814273577 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18553 : Block 2631110000000000000000 18553 18681 25477906530054814273577 25482740037941062504287 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18681 : Block 2631110000000000000000 18681 18809 25482740037941062504287 25489673198617266873179 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18809 : Block 2631110000000000000000 18809 18937 25489673198617266873179 25493908085303715133407 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18937 : Block 2631110000000000000000 18937 19065 25493908085303715133407 25499171259007863174521 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19065 : Block 2631110000000000000000 19065 19193 25499171259007863174521 25505446509350673294276 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19193 : Block 2631110000000000000000 19193 19321 25505446509350673294276 25512716997090043299720 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19321 : Block 2631110000000000000000 19321 19449 25512716997090043299720 25520446716674982738153 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19449 : Block 2631110000000000000000 19449 19577 25520446716674982738153 25528136029435988331465 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19577 : Block 2631110000000000000000 19577 19705 25528136029435988331465 25533227864326275342053 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19705 : Block 2631110000000000000000 19705 19833 25533227864326275342053 25539805781680736440896 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19833 : Block 2631110000000000000000 19833 19961 25539805781680736440896 25545838731460229509314 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19961 : Block 2631110000000000000000 19961 20089 25545838731460229509314 25553334431352190345857 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20089 : Block 2631110000000000000000 20089 20217 25553334431352190345857 25560781994749823847717 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20217 : Block 2631110000000000000000 20217 20345 25560781994749823847717 25566698936182368238003 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20345 : Block 2631110000000000000000 20345 20473 25566698936182368238003 25573073929060122406865 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20473 : Block 2631110000000000000000 20473 20601 25573073929060122406865 25579405744992750482042 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20601 : Block 2631110000000000000000 20601 20729 25579405744992750482042 25584243736810806221149 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20729 : Block 2631110000000000000000 20729 20857 25584243736810806221149 25590020388005036550881 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20857 : Block 2631110000000000000000 20857 20985 25590020388005036550881 25597190196148219525993 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20985 : Block 2631110000000000000000 20985 21113 25597190196148219525993 25603367136559811439593 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21113 : Block 2631110000000000000000 21113 21241 25603367136559811439593 25609978720784788498840 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21241 : Block 2631110000000000000000 21241 21369 25609978720784788498840 25614672773140129198035 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21369 : Block 2631110000000000000000 21369 21497 25614672773140129198035 25621206002846523890234 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21497 : Block 2631110000000000000000 21497 21625 25621206002846523890234 25629553661635436290215 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21625 : Block 2631110000000000000000 21625 21753 25629553661635436290215 25634623203587922373431 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21753 : Block 2631110000000000000000 21753 21881 25634623203587922373431 25641040025553414673251 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21881 : Block 2631110000000000000000 21881 22009 25641040025553414673251 25646051992254759736017 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b22009 : Block 2631110000000000000000 22009 22027 25646051992254759736017 25646506269272885389041 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem late : Block 2631110000000000000000 7200 22027 24466939465308081152893 25646506269272885389041 := (join (join (join (join (join (join (join (join b7200 b7219) (join b7237 b7247)) (join (join b7253 b7283) (join b7309 b7333))) (join (join (join b7369 b7433) (join b7489 b7537)) (join (join b7573 b7591) (join b7607 b7621)))) (join (join (join (join b7643 b7673) (join b7691 b7703)) (join (join b7717 b7727) (join b7741 b7753))) (join (join (join b7759 b7789) (join b7823 b7867)) (join (join b7901 b7927) (join b7949 b7993))))) (join (join (join (join (join b8053 b8093) (join b8147 b8209)) (join (join b8263 b8297) (join b8353 b8419))) (join (join (join b8467 b8539) (join b8623 b8689)) (join (join b8737 b8783) (join b8831 b8863)))) (join (join (join (join b8923 b8969) (join b9011 b9049)) (join (join b9103 b9157) (join b9203 b9241))) (join (join (join b9283 b9337) (join b9391 b9431)) (join (join b9461 b9473) (join b9491 b9511)))))) (join (join (join (join (join (join b9533 b9547) (join b9587 b9623)) (join (join b9649 b9679) (join b9719 b9749))) (join (join (join b9781 b9803) (join b9829 b9851)) (join (join b9859 b9871) (join b9883 b9901)))) (join (join (join (join b9923 b9931) (join b9941 b9949)) (join (join b9967 b10007) (join b10061 b10099))) (join (join (join b10139 b10163) (join b10181 b10211)) (join (join b10247 b10271) (join b10301 b10321))))) (join (join (join (join (join b10333 b10337) (join b10343 b10357)) (join (join b10369 b10391) (join b10429 b10459))) (join (join (join b10487 b10513) (join b10559 b10607)) (join (join b10651 b10691) (join b10729 b10771)))) (join (join (join (join b10837 b10889) (join b10949 b11003)) (join (join b11071 b11131) (join b11197 b11273))) (join (join (join b11351 b11443) (join b11527 b11633)) (join (join b11761 b11887) (join b11981 b12101))))))) (join (join (join (join (join (join (join b12211 b12323) (join b12433 b12527)) (join (join b12611 b12689) (join b12763 b12841))) (join (join (join b12919 b13001) (join b13063 b13147)) (join (join b13219 b13309) (join b13399 b13487)))) (join (join (join (join b13597 b13697) (join b13781 b13877)) (join (join b13963 b14057) (join b14173 b14301))) (join (join (join b14429 b14557) (join b14685 b14797)) (join (join b14897 b15025) (join b15149 b15271))))) (join (join (join (join (join b15373 b15467) (join b15569 b15661)) (join (join b15749 b15817) (join b15901 b15991))) (join (join (join b16073 b16141) (join b16231 b16349)) (join (join b16453 b16573) (join b16693 b16821)))) (join (join (join (join b16949 b17077) (join b17205 b17333)) (join (join b17461 b17589) (join b17717 b17845))) (join (join (join b17973 b18101) (join b18229 b18341)) (join (join b18451 b18553) (join b18681 b18809)))))) (join (join (join (join (join b18937 b19065) (join b19193 b19321)) (join (join b19449 b19577) (join b19705 b19833))) (join (join (join b19961 b20089) (join b20217 b20345)) (join (join b20473 b20601) (join b20729 b20857)))) (join (join (join (join b20985 b21113) (join b21241 b21369)) (join (join b21497 b21625) (join b21753 b21881))) b22009))))

end MertensGridUpper

open MertensGridUpper in
theorem Conjectures.Cuts.Taskabc64269ad130e923b36a98e :
  ∀ (x : ℕ), 2 ≤ x → x ≤ ⌈Real.exp (10 : ℝ)⌉₊ →
    ∑ p ∈ Finset.range x with Nat.Prime p, (1 : ℝ)/p ≤
      Real.log (Real.log ((max 2 (x-1):ℕ):ℝ)) + 0.261497 +
       if 8.9 < Real.log (x:ℝ) then 1614e-6 else 1 := by
  intro x hx hupper
  change S x ≤ _
  have h10 : Real.exp (10:ℝ) = (Real.exp 1)^10 := by simpa using Real.exp_nat_mul 1 10
  have hcap : ⌈Real.exp (10:ℝ)⌉₊ ≤ 22027 := by
    apply Nat.ceil_le.mpr
    rw [h10]
    exact (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 10).trans (by norm_num)
  obtain ⟨h7200,he⟩ := early start_S
  by_cases hu : x ≤ 7200
  · have hsmall := (Real.log_le_log (by positivity : (0:ℝ)<x)
        (by exact_mod_cast hu : (x:ℝ) ≤ 7200)).trans log_cut
    rw [ite_eq_right (not_lt.mpr hsmall)]
    by_cases hx3 : 3 < x
    · have h := he x hx3 hu
      norm_num [D] at h ⊢
      linarith
    · have h2 : max 2 (x-1)=2 := by omega
      rw [h2]
      have hm := (S_mono (show x≤3 by omega)).trans start_S
      have hh := Real.log_le_log (by norm_num : (0:ℝ)<2⁻¹) (by linarith [Real.log_two_gt_d9] : (2:ℝ)⁻¹ ≤ Real.log 2)
      rw [Real.log_inv] at hh
      norm_num [D] at hm ⊢
      linarith [Real.log_two_lt_d9]
  · have h := (late h7200).2 x (by omega) (hupper.trans hcap)
    split_ifs <;> norm_num [D] at h ⊢ <;> linarith
