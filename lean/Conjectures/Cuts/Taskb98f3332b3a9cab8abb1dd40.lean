import Mathlib

open Finset

private def lastDigit (toggle : Bool) (u : ℕ) : ℕ :=
  if toggle then 1-u%2 else u%2

private def encodeWord (S : Finset ℕ) (b : Fin 2) : ℕ → ℕ
  | 0 => b.val
  | n+1 => let u := encodeWord S b n
           2*u + lastDigit (decide (n ∈ S)) u

private theorem digit_lt (s : Bool) (u : ℕ) : lastDigit s u < 2 := by
  cases s <;> simp [lastDigit] <;> omega

private theorem word_lt (S : Finset ℕ) (b : Fin 2) (n : ℕ) :
    encodeWord S b n < 2^(n+1) := by
  induction n with
  | zero => simpa [encodeWord] using b.isLt
  | succ n ih =>
    simp only [encodeWord,pow_succ]
    have := digit_lt (decide (n ∈ S)) (encodeWord S b n)
    omega

private theorem word_recovery (n : ℕ) (S T : Finset ℕ) (b c : Fin 2)
    (h : encodeWord S b n = encodeWord T c n) :
    b = c ∧ ∀ i < n, (i ∈ S ↔ i ∈ T) := by
  induction n with
  | zero => exact ⟨Fin.ext h, by omega⟩
  | succ n ih =>
    let u := encodeWord S b n
    let v := encodeWord T c n
    change 2*u+lastDigit (decide (n ∈ S)) u = 2*v+lastDigit (decide (n ∈ T)) v at h
    have h1 := digit_lt (decide (n ∈ S)) u
    have h2 := digit_lt (decide (n ∈ T)) v
    have uv : u=v := by omega
    obtain ⟨bc,old⟩ := ih uv
    refine ⟨bc,fun i hi => ?_⟩
    by_cases lt : i<n
    · exact old i lt
    have : i=n := by omega
    subst i
    rw [←uv] at h
    by_cases hs : n ∈ S <;> by_cases ht : n ∈ T <;> simp [hs,ht,lastDigit] at h ⊢ <;> omega

private def transitionFamily (n k : ℕ) : Finset ℕ :=
  ((univ : Finset (Fin 2)) ×ˢ (range n).powersetCard k).image
    (fun p => encodeWord p.2 p.1 n)

private theorem family_size (n k : ℕ) :
    (transitionFamily n k).card = 2 * n.choose k := by
  unfold transitionFamily
  rw [card_image_of_injOn]
  · simp
  · intro a ha b hb eq
    obtain ⟨h₁,h₂⟩ := word_recovery n a.2 b.2 a.1 b.1 eq
    have hA := (mem_powersetCard.mp (mem_product.mp ha).2).1
    have hB := (mem_powersetCard.mp (mem_product.mp hb).2).1
    apply Prod.ext h₁
    ext i
    by_cases hi : i<n
    · exact h₂ i hi
    · constructor <;> intro h
      · exact (hi (mem_range.mp (hA h))).elim
      · exact (hi (mem_range.mp (hB h))).elim

private theorem family_range (n k : ℕ) :
    transitionFamily n k ⊆ range (2^(n+1)) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := mem_image.mp hx
  exact mem_range.mpr (word_lt _ _ _)

private noncomputable def cosPolynomial (x : ℝ) : ℝ :=
  ∑ j ∈ range 8, (-1:ℝ)^j * x^(2*j) / (Nat.factorial (2*j):ℝ)

private theorem cos_lower_on_half_turn {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ 22/7) :
    cosPolynomial x - (22/7:ℝ)^16 / (16:ℕ).factorial ≤ Real.cos x := by
  by_cases h0 : x=0
  · subst x
    norm_num [cosPolynomial,Finset.sum_range_succ,Nat.factorial]
  obtain ⟨y,_,eqn⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f:=Real.cos)
    (n:=15) (Ne.symm h0) Real.contDiff_cos.contDiffOn
  have hpoly : taylorWithinEval Real.cos 15 (Set.uIcc 0 x) 0 x = cosPolynomial x := by
    rw [taylor_within_apply]
    have deriv (j : ℕ) : iteratedDerivWithin j Real.cos (Set.uIcc 0 x) 0 =
        iteratedDeriv j Real.cos 0 := iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_uIcc (Ne.symm h0)) Real.contDiff_cos.contDiffAt Set.left_mem_uIcc
    simp_rw [deriv]
    norm_num [cosPolynomial,Finset.sum_range_succ,Nat.factorial,iteratedDeriv_succ] <;> ring
  rw [hpoly,sub_zero] at eqn
  have bd := (abs_le.mp (Real.abs_iteratedDeriv_cos_le_one 16 y)).1
  have h1 := mul_le_mul_of_nonneg_right bd (pow_nonneg hx 16)
  have h2 := pow_le_pow_left₀ hx hu 16
  norm_num [Nat.factorial] at eqn h1 h2 ⊢
  linarith

private theorem rational_phase_lower (f : ℝ) (hf : 0 ≤ f) (hh : f ≤ 1/2) :
    cosPolynomial (2*(314159/100000)*f) - (22/7:ℝ)^16 / (16:ℕ).factorial - 1/100000 ≤
      Real.cos (2*Real.pi*f) := by
  have approx := cos_lower_on_half_turn (x:=2*(314159/100000)*f) (by positivity) (by linarith)
  have err := Real.abs_cos_sub_cos_le (2*(314159/100000)*f) (2*Real.pi*f)
  have pl : 0 ≤ Real.pi - 314159/100000 := by linarith [Real.pi_gt_d6]
  have pu : Real.pi - 314159/100000 ≤ 1/100000 := by linarith [Real.pi_lt_d6]
  have mp := mul_le_mul pu hh hf (by norm_num : (0:ℝ) ≤ 1/100000)
  rw [abs_of_nonpos (by nlinarith [mul_nonneg pl hf] : 2*(314159/100000)*f - 2*Real.pi*f ≤ 0)] at err
  linarith [(abs_le.mp err).2]

private theorem error_budget {t : ℕ} (ht : 2000 ≤ t) :
    (7452/10000 : ℝ) - 210/(1000*(t:ℝ)) - 30/(1000*(t:ℝ)+1) > 745/1000 := by
  have h : (2000:ℝ) ≤ t := by exact_mod_cast ht
  have a : 210/(1000*(t:ℝ)) ≤ 210/(2000000:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have b : 30/(1000*(t:ℝ)+1) ≤ 30/(2000001:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith

private theorem repeat_count (n k : ℕ) (hk : k ≤ n) :
    n * n^k ≤ n * n.descFactorial k + k.choose 2 * n^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hn : k ≤ n := by omega
    have prev := Nat.mul_le_mul_right n (ih hn)
    have cost := Nat.mul_le_mul_left (n*k) (Nat.descFactorial_le_pow n k)
    have restore := Nat.sub_add_cancel hn
    rw [Nat.descFactorial_succ, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right]
    have step : (n-k)*n.descFactorial k + k*n.descFactorial k = n*n.descFactorial k := by
      rw [←Nat.add_mul,restore]
    nlinarith only [prev,cost,congrArg (fun z : ℕ => n*z) step]

private theorem repeat_rate (n : ℕ) (hn : 15 ≤ n) :
    1 - (n.descFactorial 15 : ℝ)/(n:ℝ)^15 ≤ 105/(n:ℝ) := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have h := repeat_count n 15 hn
  rw [show Nat.choose 15 2 = 105 by decide] at h
  have hr : (n:ℝ)*n^15 ≤ n*(n.descFactorial 15:ℝ)+105*n^15 := by exact_mod_cast h
  rw [le_div_iff₀ hp,sub_mul,one_mul,sub_le_iff_le_add]
  rw [div_mul_eq_mul_div,← mul_div_cancel_right₀ (105:ℝ) (pow_ne_zero 15 hp.ne') ,
    ←add_div, le_div_iff₀ (pow_pos hp 15)]
  linarith only [hr]
private theorem average_restrict_lower {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hs : S.Nonempty) (f : α → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ x, f x)/(Fintype.card α:ℝ) - 2*(1-(S.card:ℝ)/Fintype.card α) ≤
      (∑ x ∈ S, f x)/(S.card:ℝ) := by
  let m : ℝ := S.card
  let n : ℝ := Fintype.card α
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Finset.card_pos.mpr hs
  have hmn : m ≤ n := by dsimp [m,n]; exact_mod_cast Finset.card_le_univ S
  have hn : 0 < n := hm.trans_le hmn
  have lo : -m ≤ ∑ x ∈ S, f x := by
    calc
      _ = ∑ _x ∈ S, (-1:ℝ) := by simp [m]
      _ ≤ _ := sum_le_sum fun x _ => (abs_le.mp (hf x)).1
  have up : ∑ x ∈ Sᶜ, f x ≤ n-m := by
    calc
      _ ≤ ∑ _x ∈ Sᶜ, (1:ℝ) := sum_le_sum fun x _ => (abs_le.mp (hf x)).2
      _ = _ := by simp [n,m,Finset.card_compl,Nat.cast_sub (Finset.card_le_univ S)]
  have total := Finset.sum_add_sum_compl S f
  change _ / n - 2*(1-m/n) ≤ _ / m
  rw [le_div_iff₀ hm]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right up hm.le,
    mul_le_mul_of_nonneg_right lo (sub_nonneg.mpr hmn),
    congrArg (fun z : ℝ => z*m) total]

private theorem positions_without_replacement (n : ℕ) (hn : 15 ≤ n)
    (f : (Fin 15 → Fin n) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ x, f x)/(n:ℝ)^15 - 210/(n:ℝ) ≤
      (∑ e : Fin 15 ↪ Fin n, f e)/(n.descFactorial 15:ℝ) := by
  classical
  let inj : (Fin 15 ↪ Fin n) ↪ (Fin 15 → Fin n) := ⟨fun e => e, fun _ _ h => DFunLike.coe_injective h⟩
  let S := Finset.univ.map inj
  have hs : S.Nonempty := ⟨_,Finset.mem_map.mpr ⟨Fin.castLEEmb hn,Finset.mem_univ _,rfl⟩⟩
  have h := average_restrict_lower S hs f hf
  have size : S.card = n.descFactorial 15 := by simp [S,Fintype.card_embedding_eq]
  rw [size] at h
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] at h
  have sum_eq : (∑ x ∈ S, f x) = ∑ e : Fin 15 ↪ Fin n, f e := by rw [Finset.sum_map]; rfl
  rw [sum_eq] at h
  have r := repeat_rate n hn
  rw [show (210:ℝ)/n = 2*(105/n) by ring]
  linarith

private theorem drop_digits (S : Finset ℕ) (b : Fin 2) (n r : ℕ) :
    encodeWord S b (n+r) / 2^r = encodeWord S b n := by
  induction r with
  | zero => simp
  | succ r ih =>
    have step : encodeWord S b (n+r+1) / 2 = encodeWord S b (n+r) := by
      simp only [encodeWord]
      have := digit_lt (decide (n+r ∈ S)) (encodeWord S b (n+r))
      omega
    rw [pow_succ',←Nat.div_div_eq_div_mul]
    exact (congrArg (fun k : ℕ => k/2^r) step).trans ih

private theorem complete_window_phase (w j r : ℕ) :
    (Complex.exp (↑((2:ℝ)*Real.pi*↑⌊(65536:ℝ)*2^j*((w:ℝ)/2^(j+16+r))⌋/65536) *
      Complex.I)).re =
    Real.cos (2*Real.pi*((w/2^r)%65536:ℕ)/65536) := by
  have scale : (65536:ℝ)*2^j*((w:ℝ)/2^(j+16+r)) = (w:ℝ)/(2^r:ℕ) := by
    push_cast
    rw [pow_add,pow_add]
    norm_num
    field_simp
  rw [scale, Int.floor_div_natCast,Int.floor_natCast,←Int.natCast_ediv,Complex.exp_ofReal_mul_I_re]
  let z := w/2^r
  have h : (z:ℝ) = ((z%65536:ℕ):ℝ)+65536*((z/65536:ℕ):ℝ) := by
    exact_mod_cast (Nat.mod_add_div z 65536).symm
  change Real.cos (2*Real.pi*(z:ℝ)/65536) = _
  rw [show 2*Real.pi*(z:ℝ)/65536 = 2*Real.pi*((z%65536:ℕ):ℝ)/65536 +
      (z/65536:ℕ)*(2*Real.pi) by linear_combination (Real.pi/32768)*h]
  exact Real.cos_add_nat_mul_two_pi _ _

private theorem local_word (n k : ℕ) (S T : Finset ℕ) (b : Fin 2)
    (agree : ∀ i < k, i ∈ T ↔ n+i ∈ S) :
    encodeWord S b (n+k) % 2^(k+1) =
      encodeWord T ⟨encodeWord S b n % 2, Nat.mod_lt _ (by decide)⟩ k := by
  induction k with
  | zero => simp [encodeWord]
  | succ k ih =>
    let u := encodeWord S b (n+k)
    let M := 2^(k+1)
    have hm : 0 < M := by dsimp [M]; positivity
    have he := ih (fun i hi => agree i (by omega))
    have hpar : (u%M)%2 = u%2 := Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : k+1 ≠ 0))
    have flag : decide (n+k ∈ S) = decide (k ∈ T) := by simp [agree k (by omega)]
    change (2*u+lastDigit (decide (n+k ∈ S)) u) % (2^(k+1+1)) = _
    rw [pow_succ']
    simp only [encodeWord,←he,flag]
    let d := lastDigit (decide (k ∈ T)) u
    have hsmall : 2*(u%M)+d < 2*M := by
      have := Nat.mod_lt u hm
      have := digit_lt (decide (k ∈ T)) u
      dsimp [d]; omega
    have deq : lastDigit (decide (k ∈ T)) (u%M) = d := by simp [d,lastDigit,hpar]
    change (2*u+d)%(2*M) = 2*(u%M)+lastDigit (decide (k ∈ T)) (u%M)
    rw [deq]
    have ee : 2*u+d = (2*(u%M)+d)+(2*M)*(u/M) := by
      have h := Nat.mod_add_div u M
      nlinarith only [h]
    rw [ee,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hsmall]

private noncomputable def phaseTerm (L w j : ℕ) : ℂ :=
  Complex.exp (↑((2:ℝ)*Real.pi*↑⌊(65536:ℝ)*2^j*((w:ℝ)/2^L)⌋/65536)*Complex.I)

private theorem interior_phase (j r : ℕ) (S T : Finset ℕ) (b : Fin 2)
    (agree : ∀ i < 15, i ∈ T ↔ j+i ∈ S) :
    (phaseTerm (j+16+r) (encodeWord S b (j+15+r)) j).re =
      Real.cos (2*Real.pi*(encodeWord T ⟨encodeWord S b j % 2,Nat.mod_lt _ (by decide)⟩ 15:ℕ)/65536) := by
  unfold phaseTerm
  rw [complete_window_phase,drop_digits]
  exact congrArg (fun z : ℕ => Real.cos (2*Real.pi*z/65536)) (local_word j 15 S T b agree)

private theorem boundary_sum (L w : ℕ) (hL : 15 ≤ L) :
    (∑ j ∈ range (L-15), (phaseTerm L w j).re) - 15 ≤
      (∑ j ∈ range L, phaseTerm L w j).re := by
  rw [Complex.re_sum]
  conv_rhs => enter [1]; rw [show L = (L-15)+15 by omega]
  rw [sum_range_add]
  have h : ∀ j, (-1:ℝ) ≤ (phaseTerm L w j).re := by
    intro j
    unfold phaseTerm
    rw [Complex.exp_ofReal_mul_I_re]
    exact Real.neg_one_le_cos _
  have hh := sum_le_sum (s:=range 15) fun j _ => h (L-15+j)
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_ofNat] at hh
  linarith

private def atBit (S : Finset ℕ) (j : ℕ) (b : Fin 2) : Fin 2 :=
  ⟨encodeWord S b j % 2, Nat.mod_lt _ (by decide)⟩

private theorem atBit_injective (S : Finset ℕ) (j : ℕ) : Function.Injective (atBit S j) := by
  induction j with
  | zero =>
    intro a b h
    apply Fin.ext
    simpa [atBit,encodeWord,Nat.mod_eq_of_lt a.isLt,Nat.mod_eq_of_lt b.isLt] using congrArg Fin.val h
  | succ j ih =>
    intro a b h
    apply ih
    apply Fin.ext
    have eq := congrArg Fin.val h
    change (2*encodeWord S a j + lastDigit (decide (j ∈ S)) (encodeWord S a j)) % 2 =
      (2*encodeWord S b j + lastDigit (decide (j ∈ S)) (encodeWord S b j)) % 2 at eq
    change encodeWord S a j % 2 = encodeWord S b j % 2
    by_cases hS : j ∈ S <;> simp [lastDigit,hS] at eq <;> omega

private theorem phase_seed_sum (j r : ℕ) (S T : Finset ℕ)
    (agree : ∀ i < 15, i ∈ T ↔ j+i ∈ S) :
    (∑ b : Fin 2, (phaseTerm (j+16+r) (encodeWord S b (j+15+r)) j).re) =
    ∑ b : Fin 2, Real.cos (2*Real.pi*(encodeWord T b 15:ℕ)/65536) := by
  let e := Equiv.ofBijective (atBit S j)
    ((Finite.injective_iff_bijective).mp (atBit_injective S j))
  calc
    _ = ∑ b : Fin 2, Real.cos (2*Real.pi*(encodeWord T (e b) 15:ℕ)/65536) :=
      sum_congr rfl fun b _ => interior_phase j r S T b agree
    _ = _ := Equiv.sum_comp e (fun b : Fin 2 => Real.cos (2*Real.pi*(encodeWord T b 15:ℕ)/65536))

private theorem uniform_double_average {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) (a : α) (b : β)
    (rows : ∀ x, ∑ y, F x y = ∑ y, F a y)
    (cols : ∀ y, ∑ x, F x y = ∑ x, F x b) :
    (∑ x, F x b)/(Fintype.card α:ℝ) = (∑ y, F a y)/(Fintype.card β:ℝ) := by
  have hA : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  have hB : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨b⟩
  have eq : (Fintype.card α:ℝ)*(∑ y, F a y) = (Fintype.card β:ℝ)*(∑ x, F x b) := by
    calc
      _ = ∑ x, ∑ y, F x y := by simp_rw [rows]; simp
      _ = ∑ y, ∑ x, F x y := sum_comm
      _ = _ := by simp_rw [cols]; simp
  apply (div_eq_div_iff (by exact_mod_cast hA.ne') (by exact_mod_cast hB.ne')).mpr
  linarith

private theorem sampling_rows {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card)
    (G : (Fin 15 → Bool) → ℝ) :
    (∑ e : Fin 15 ↪ Fin n, G (fun i => decide (e i ∈ S))) =
    ∑ e : Fin 15 ↪ Fin n, G (fun i => decide (e i ∈ T)) := by
  obtain ⟨σ, rfl⟩ := Equiv.Perm.exists_map_finset_eq S T h
  let E := (Equiv.refl (Fin 15)).embeddingCongr σ
  let F := fun (e : Fin 15 ↪ Fin n) => G (fun i => decide (e i ∈ S.map σ.toEmbedding))
  calc
    _ = ∑ e, F (E e) := by
      apply sum_congr rfl
      intro e _
      congr 1
      funext i
      change decide (e i ∈ S) = decide (σ (e i) ∈ S.map σ.toEmbedding)
      simp
    _ = _ := Equiv.sum_comp E F

private theorem sampling_cols {n k : ℕ} (e f : Fin 15 ↪ Fin n)
    (G : (Fin 15 → Bool) → ℝ) :
    (∑ S : {S : Finset (Fin n) // S.card = k}, G (fun i => decide (e i ∈ S.val))) =
    ∑ S : {S : Finset (Fin n) // S.card = k}, G (fun i => decide (f i ∈ S.val)) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair e f e.injective f.injective
  let E := σ.finsetCongr.subtypeEquiv (p := fun S => S.card = k)
    (q := fun S => S.card = k) (fun S => by simp [Equiv.finsetCongr_apply])
  let F := fun S : {S : Finset (Fin n) // S.card = k} => G (fun i => decide (f i ∈ S.val))
  calc
    _ = ∑ S, F (E S) := by
      apply sum_congr rfl
      intro S _
      congr 1
      funext i
      change decide (e i ∈ S.val) = decide (f i ∈ S.val.map σ.toEmbedding)
      rw [← hσ i]
      simp
    _ = _ := Equiv.sum_comp E F

private theorem sampling_average {n k : ℕ} (S : {S : Finset (Fin n) // S.card = k})
    (e : Fin 15 ↪ Fin n) (G : (Fin 15 → Bool) → ℝ) :
    (∑ T : {T : Finset (Fin n) // T.card = k}, G (fun i => decide (e i ∈ T.val))) /
      (Fintype.card {T : Finset (Fin n) // T.card = k} : ℝ) =
    (∑ f : Fin 15 ↪ Fin n, G (fun i => decide (f i ∈ S.val))) /
      (Fintype.card (Fin 15 ↪ Fin n) : ℝ) :=
  uniform_double_average (fun T f => G (fun i => decide (f i ∈ T.val))) S e
    (fun T => sampling_rows T.val S.val (T.property.trans S.property.symm) G)
    (fun f => sampling_cols f e G)

private theorem fixed_window_lower {n k : ℕ} (hn : 15 ≤ n)
    (S : {S : Finset (Fin n) // S.card = k}) (e : Fin 15 ↪ Fin n)
    (G : (Fin 15 → Bool) → ℝ) (hG : ∀ b, |G b| ≤ 1) :
    (∑ x : Fin 15 → Fin n, G (fun i => decide (x i ∈ S.val))) / (n : ℝ)^15 -
      210 / (n : ℝ) ≤
    (∑ T : {T : Finset (Fin n) // T.card = k}, G (fun i => decide (e i ∈ T.val))) /
      (Fintype.card {T : Finset (Fin n) // T.card = k} : ℝ) := by
  rw [sampling_average S e G]
  simpa only [Fintype.card_embedding_eq, Fintype.card_fin] using
    positions_without_replacement n hn (fun x => G (fun i => decide (x i ∈ S.val)))
      (fun x => hG _)

private theorem iid_pattern_sum {n : ℕ} (S : Finset (Fin n)) (G : (Fin 15 → Bool) → ℝ) :
    (∑ x : Fin 15 → Fin n, G (fun i => decide (x i ∈ S))) =
    ∑ b : Fin 15 → Bool, ((∏ i, if b i then S.card else n - S.card : ℕ) : ℝ) * G b := by
  classical
  let flags := fun (x : Fin 15 → Fin n) (i : Fin 15) => decide (x i ∈ S)
  have fiber (b : Fin 15 → Bool) :
      (univ.filter (fun x => flags x = b)) =
        Fintype.piFinset (fun i => if b i then S else Sᶜ) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff, flags]
    apply forall_congr'
    intro i
    cases hb : b i <;> simp [hb]
  calc
    _ = ∑ b, ∑ x ∈ univ.filter (fun x => flags x = b), G (flags x) :=
      (sum_fiberwise_of_maps_to (fun x _ => mem_univ (flags x)) (fun x => G (flags x))).symm
    _ = _ := by
      apply sum_congr rfl
      intro b _
      rw [sum_congr rfl (fun x hx => congrArg G (mem_filter.mp hx).2), sum_const,
        nsmul_eq_mul, fiber, Fintype.card_piFinset]
      congr 2
      apply prod_congr rfl
      intro i _
      cases hb : b i <;> simp [hb, Finset.card_compl]

private noncomputable def modelMean (G : (Fin 15 → Bool) → ℝ) : ℝ :=
  (∑ b : Fin 15 → Bool, ((∏ i, if b i then 17 else 183 : ℕ) : ℝ) * G b) / 200^15

private theorem iid_model_mean {t : ℕ} (ht : 0 < t) (S : Finset (Fin (1000*t)))
    (hS : S.card = 85*t) (G : (Fin 15 → Bool) → ℝ) :
    (∑ x : Fin 15 → Fin (1000*t), G (fun i => decide (x i ∈ S))) /
      ((1000*t : ℕ) : ℝ)^15 = modelMean G := by
  rw [iid_pattern_sum, modelMean, div_eq_div_iff (by positivity) (by positivity)]
  rw [sum_mul, sum_mul]
  apply sum_congr rfl
  intro b _
  have scale : (∏ i, if b i then S.card else 1000*t-S.card : ℕ) =
      (∏ i, if b i then 17 else 183 : ℕ) * (5*t)^15 := by
    have term (i : Fin 15) : (if b i then S.card else 1000*t-S.card) =
        (if b i then 17 else 183)*(5*t) := by
      cases hb : b i <;> simp [hS] <;> omega
    simp_rw [term]
    rw [prod_mul_distrib]; simp only [prod_const, card_univ, Fintype.card_fin]
  rw [scale]
  push_cast
  ring

private theorem model_window_lower {t : ℕ} (ht : 0 < t)
    (S : {S : Finset (Fin (1000*t)) // S.card = 85*t}) (e : Fin 15 ↪ Fin (1000*t))
    (G : (Fin 15 → Bool) → ℝ) (hG : ∀ b, |G b| ≤ 1) :
    modelMean G - 210 / ((1000*t : ℕ) : ℝ) ≤
    (∑ T : {T : Finset (Fin (1000*t)) // T.card = 85*t}, G (fun i => decide (e i ∈ T.val))) /
      (Fintype.card {T : Finset (Fin (1000*t)) // T.card = 85*t} : ℝ) := by
  rw [← iid_model_mean ht S.val S.property]
  exact fixed_window_lower (by omega) S e G hG

private def flipSet (flags : Fin 15 → Bool) : Finset ℕ :=
  (univ.filter (fun i => flags i = true)).map Fin.valEmbedding

private noncomputable def windowCos (flags : Fin 15 → Bool) : ℝ :=
  (∑ b : Fin 2, Real.cos (2*Real.pi*(encodeWord (flipSet flags) b 15:ℕ)/65536)) / 2

private theorem windowCos_abs (flags : Fin 15 → Bool) : |windowCos flags| ≤ 1 := by
  unfold windowCos
  rw [Fin.sum_univ_two]
  apply abs_le.mpr
  constructor <;> linarith [Real.neg_one_le_cos (2*Real.pi*(encodeWord (flipSet flags) 0 15:ℕ)/65536),
    Real.neg_one_le_cos (2*Real.pi*(encodeWord (flipSet flags) 1 15:ℕ)/65536),
    Real.cos_le_one (2*Real.pi*(encodeWord (flipSet flags) 0 15:ℕ)/65536),
    Real.cos_le_one (2*Real.pi*(encodeWord (flipSet flags) 1 15:ℕ)/65536)]

private theorem word_window_cos (j r : ℕ) (S : Finset ℕ) :
    (∑ b : Fin 2, (phaseTerm (j+16+r) (encodeWord S b (j+15+r)) j).re) / 2 =
      windowCos (fun i => decide (j+i.val ∈ S)) := by
  unfold windowCos
  congr 1
  apply phase_seed_sum
  intro i hi
  simp only [flipSet, mem_map, mem_filter, mem_univ, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro h
    exact ⟨⟨i,hi⟩, h, rfl⟩

private def wordLower (w : ℕ) : ℚ :=
  let x : ℚ := 2*(314159/100000)*(min w (65536-w):ℕ)/65536
  (∑ j ∈ range 8, (-1:ℚ)^j*x^(2*j)/(Nat.factorial (2*j):ℚ)) -
    (22/7:ℚ)^16/(16:ℕ).factorial - 1/100000

private theorem wordLower_valid (w : ℕ) (hw : w ≤ 65536) :
    (wordLower w : ℝ) ≤ Real.cos (2*Real.pi*(w:ℝ)/65536) := by
  let m := min w (65536-w)
  have hm : m ≤ 32768 := by dsimp [m]; omega
  have hm' : (m:ℝ) ≤ 32768 := by exact_mod_cast hm
  have bound := rational_phase_lower ((m:ℝ)/65536) (by positivity) (by linarith)
  have angle : Real.cos (2*Real.pi*((m:ℝ)/65536)) = Real.cos (2*Real.pi*(w:ℝ)/65536) := by
    by_cases h : w ≤ 65536-w
    · simp only [m,min_eq_left h]; congr 1; ring
    · have eq : (m:ℝ) = 65536-(w:ℝ) := by
        dsimp [m]; rw [min_eq_right (by omega),Nat.cast_sub hw]; norm_num
      rw [eq,show 2*Real.pi*((65536-(w:ℝ))/65536) =
        2*Real.pi-(2*Real.pi*(w:ℝ)/65536) by ring,Real.cos_two_pi_sub]
  rw [angle] at bound
  convert bound using 1
  unfold wordLower cosPolynomial
  push_cast
  dsimp [m]
  push_cast
  ring_nf

private def windowCertificate : ℚ :=
  (∑ f : Fin 15 → Bool, ((∏ i, if f i then 17 else 183 : ℕ) : ℚ) *
    ((∑ b : Fin 2, wordLower (encodeWord (flipSet f) b 15))/2)) / 200^15

private theorem windowCertificate_valid :
    (windowCertificate : ℝ) ≤ modelMean windowCos := by
  unfold windowCertificate modelMean windowCos
  push_cast
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro f _
  simp only [apply_ite Rat.cast, Rat.cast_ofNat]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => by split <;> norm_num)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply sum_le_sum
  intro b _
  apply wordLower_valid
  exact (word_lt (flipSet f) b 15).le

private def certDen : ℕ := 143020185321451577675345214649553751120619783734382265528116412684748869593841547608064000000000000000000000000000000000000000000000000000000000000000000000000

private def certNum (m : ℕ) : ℤ :=
  let z : ℤ := m
  (143018135718465117217316192402053005256137952106674519547793204506722243668130468587750031360000000000000000000000000000000000000000000000000000000000000000000) * z^0 + (-657304313927509935900089822912726571877203248632575943083769368073713321878447090093260800000000000000000000000000000000000000000000000000000000000000) * z^2 + (503482498101745885513594385229295458885998446715803555659239973983961230284302079450152960000000000000000000000000000000000000000000000000000) * z^4 + (-154263174924320315844368149532008865402089691616034648109996696083653315424923036167228620800000000000000000000000000000000000000000) * z^6 + (25320564299070399977850393094781328127600869504287988948150558706485568095608927619561553920000000000000000000000000000000) * z^8 + (-2586008884371488022507797010926061788379203244158069562279672893806138932251462087147205427200000000000000000000) * z^10 + (180075746240929743250204659191282812075927370480446535589212934492150852923709528905864970240000000000) * z^12 + (-9094586898971522472125937160103119830759709174492597665205106021496217901469421030658558883) * z^14

private theorem certNum_exact (w : ℕ) :
    wordLower w = (certNum (min w (65536-w)) : ℚ) / certDen := by
  unfold wordLower certNum certDen
  generalize min w (65536-w) = m
  push_cast
  norm_num [Finset.sum_range_succ, Nat.factorial] <;> ring

private def certTree : ℕ → ℕ → ℤ
  | 0, w => certNum (min w (65536-w))
  | k+1, w =>
    let a := certTree k (2*w)
    let b := certTree k (2*w+1)
    if w%2 = 0 then 183*a+17*b else 17*a+183*b

private theorem certTree_toggle (k w : ℕ) :
    certTree (k+1) w =
      183 * certTree k (2*w + lastDigit false w) +
       17 * certTree k (2*w + lastDigit true w) := by
  have h := Nat.mod_lt w (by decide : 0 < 2)
  rcases (by omega : w%2 = 0 ∨ w%2 = 1) with hw | hw
  · simp [certTree,lastDigit,hw]
  · simp [certTree,lastDigit,hw,add_comm]

private theorem sum_flags_succ (n : ℕ) (F : (Fin (n+1) → Bool) → ℤ) :
    (∑ f, F f) = (∑ f, F (Fin.cons false f)) + ∑ f, F (Fin.cons true f) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp F, Fintype.sum_prod_type]
  simp [Fin.consEquiv_apply, add_comm]

private def applyFlags : (k : ℕ) → ℕ → (Fin k → Bool) → ℕ
  | 0, w, _ => w
  | k+1, w, f => applyFlags k (2*w + lastDigit (f 0) w) (fun i => f i.succ)

private theorem tree_flags (k w : ℕ) :
    certTree k w = ∑ f : Fin k → Bool, (∏ i, if f i then (17:ℤ) else 183) *
      certNum (min (applyFlags k w f) (65536-applyFlags k w f)) := by
  induction k generalizing w with
  | zero => simp [certTree,applyFlags]
  | succ k ih =>
    rw [certTree_toggle, sum_flags_succ, ih, ih, mul_sum, mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intro f _ <;>
      simp [Fin.prod_univ_succ, applyFlags, mul_assoc]

private theorem flags_extend (S : Finset ℕ) (b : Fin 2) (k j : ℕ)
    (f : Fin k → Bool) (agree : ∀ i, f i = decide (j+i.val ∈ S)) :
    applyFlags k (encodeWord S b j) f = encodeWord S b (j+k) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h0 := agree 0
    simp only [Fin.val_zero, Nat.add_zero] at h0
    simp only [applyFlags, h0]
    change applyFlags k (encodeWord S b (j+1)) _ = _
    rw [ih (j+1) (fun i => f i.succ) (fun i => by
      rw [agree]; simp only [Fin.val_succ]; congr 2 <;> omega)]
    congr 1 <;> omega

private theorem flags_encode (f : Fin 15 → Bool) (b : Fin 2) :
    applyFlags 15 b.val f = encodeWord (flipSet f) b 15 := by
  apply flags_extend (flipSet f) b 15 0
  intro i
  simp only [Nat.zero_add, flipSet, mem_map, mem_filter, mem_univ, true_and]
  have h : (∃ a : Fin 15, f a = true ∧ Fin.valEmbedding a = i.val) ↔ f i = true := by
    constructor
    · rintro ⟨a, ha, he⟩
      exact (Fin.ext he : a = i) ▸ ha
    · intro hi
      exact ⟨i,hi,rfl⟩
  cases hi : f i with
  | true => exact (decide_eq_true (h.mpr hi)).symm
  | false => exact (decide_eq_false (fun hp => by simpa [hi] using h.mp hp)).symm

private theorem weighted_word_sum (b : Fin 2) :
    (∑ f : Fin 15 → Bool, ((∏ i, if f i then 17 else 183 : ℕ) : ℚ) *
      wordLower (encodeWord (flipSet f) b 15)) = (certTree 15 b.val : ℚ) / certDen := by
  rw [tree_flags, Int.cast_sum, Finset.sum_div]
  apply sum_congr rfl
  intro f _
  rw [flags_encode, certNum_exact, Int.cast_mul]
  have weight : (((∏ i, if f i then (17:ℕ) else 183) : ℕ) : ℚ) =
      (((∏ i, if f i then (17:ℤ) else 183) : ℤ) : ℚ) := by
    push_cast
    apply prod_congr rfl
    intro i _
    cases h : f i <;> norm_num [h]
  rw [weight]
  ring

private theorem windowCertificate_tree :
    windowCertificate = ((certTree 15 0 + certTree 15 1 : ℤ) : ℚ) /
      (2 * 200^15 * (certDen : ℚ)) := by
  unfold windowCertificate
  simp_rw [Fin.sum_univ_two, mul_div_assoc', mul_add]
  rw [← Finset.sum_div, Finset.sum_add_distrib, weighted_word_sum, weighted_word_sum]
  push_cast
  change (( (certTree 15 0 : ℚ) / certDen + (certTree 15 1 : ℚ) / certDen) / 2) / 200^15 = _
  ring

private abbrev Masks (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

private def familyWord (n k : ℕ) : (Masks n k × Fin 2) ↪ ℕ where
  toFun p := encodeWord (p.1.val.map Fin.valEmbedding) p.2 n
  inj' := by
    rintro ⟨S,b⟩ ⟨T,c⟩ he
    obtain ⟨hbc,hst⟩ := word_recovery n _ _ _ _ he
    apply Prod.ext _ hbc
    apply Subtype.ext
    ext i
    simpa [Fin.val_inj] using hst i.val i.isLt

private def windowPos (n j : ℕ) (h : j+15 ≤ n) : Fin 15 ↪ Fin n where
  toFun i := ⟨j+i.val,by omega⟩
  inj' := by intro i k he; apply Fin.ext; have := congrArg Fin.val he; dsimp at this; omega

private theorem mask_window (n k j : ℕ) (h : j+15 ≤ n) (S : Masks n k) :
    (∑ b : Fin 2, (phaseTerm (n+1) (familyWord n k (S,b)) j).re) / 2 =
      windowCos (fun i => decide (windowPos n j h i ∈ S.val)) := by
  let r := n-(j+15)
  have h₁ : j+16+r = n+1 := by dsimp [r]; omega
  have h₂ : j+15+r = n := by dsimp [r]; omega
  have eqn := word_window_cos j r (S.val.map Fin.valEmbedding)
  rw [h₁,h₂] at eqn
  refine eqn.trans (congrArg windowCos (funext fun i => ?_))
  change decide ((windowPos n j h i).val ∈ S.val.map Fin.valEmbedding) = _
  simp [Fin.val_inj]

private theorem total_window_bound {α : Type*} [Fintype α] (L : ℕ) (hL : 15 ≤ L)
    (w : α → ℕ) (q : ℝ)
    (hw : ∀ j < L-15, q * (Fintype.card α : ℝ) ≤ ∑ a, (phaseTerm L (w a) j).re) :
    ((L-15 : ℕ) * q - 15) * (Fintype.card α : ℝ) ≤
      ∑ a, (∑ j ∈ range L, phaseTerm L (w a) j).re := by
  have hj := sum_le_sum (s := range (L-15)) (fun j hj => hw j (mem_range.mp hj))
  rw [sum_comm] at hj
  simp only [sum_const,card_range,nsmul_eq_mul] at hj
  have hb := sum_le_sum (s := (univ : Finset α)) (fun a _ => boundary_sum L (w a) hL)
  rw [sum_sub_distrib] at hb
  simp only [sum_const,card_univ,nsmul_eq_mul] at hb
  nlinarith only [hj,hb]

private theorem all_masks_at_window (t j : ℕ) (ht : 0 < t) (hj : j+15 ≤ 1000*t)
    (S : Masks (1000*t) (85*t)) :
    (modelMean windowCos - 210/((1000*t : ℕ) : ℝ)) *
      (Fintype.card (Masks (1000*t) (85*t) × Fin 2) : ℝ) ≤
    ∑ a : Masks (1000*t) (85*t) × Fin 2,
      (phaseTerm (1000*t+1) (familyWord _ _ a) j).re := by
  have hm := model_window_lower ht S (windowPos _ _ hj) windowCos windowCos_abs
  have hc : 0 < (Fintype.card (Masks (1000*t) (85*t)) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨S⟩
  have hh := (le_div_iff₀ hc).mp hm
  simp_rw [← mask_window _ _ _ hj] at hh
  rw [← sum_div] at hh
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hh
  linarith [ (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mp hh ]

set_option linter.constructorNameAsVariable false in
private theorem family_total (t : ℕ) (ht : 2000 ≤ t)
    (hm : (1863/2500 : ℝ) < modelMean windowCos) :
    let n := 1000*t
    let W := univ.map (familyWord n (85*t))
    (745/1000 : ℝ) * (n+1:ℕ) * W.card <
      ∑ w ∈ W, (∑ j ∈ range (n+1), phaseTerm (n+1) w j).re := by
  let n := 1000*t
  let A := Masks n (85*t) × Fin 2
  have hn : 2000000 ≤ n := by dsimp [n]; omega
  have hc : 0 < Fintype.card (Masks n (85*t)) := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
    exact Nat.choose_pos (by dsimp [n]; omega)
  obtain ⟨S⟩ := Fintype.card_pos_iff.mp hc
  have hA : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty A from ⟨(S,0)⟩)
  let q : ℝ := 1863/2500 - 210/(n:ℝ)
  have bound := total_window_bound (α:=A) (n+1) (by omega) (familyWord n (85*t)) q (by
    intro j hj
    exact le_trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hm.le _) hA.le)
      (all_masks_at_window t j (by omega) (by dsimp [n] at hj; omega) S))
  have hL : 0 < (n:ℝ)+1 := by positivity
  have margin := error_budget ht
  change (7452/10000:ℝ) - 210/(1000*(t:ℝ)) - 30/(1000*(t:ℝ)+1) > _ at margin
  have castn : (n:ℝ) = 1000*(t:ℝ) := by simp [n]
  rw [←castn] at margin
  have margin' : (745/1000 : ℝ)*((n:ℝ)+1) < ((n:ℝ)+1)*q - 30 := by
    have he := (div_mul_cancel₀ (30:ℝ) hL.ne')
    dsimp [q]
    nlinarith only [mul_pos (sub_pos.mpr margin) hL, he]
  have hq : q ≤ 1 := by
    dsimp [q]
    have hh : 0 ≤ 210/(n:ℝ) := by positivity
    linarith only [hh]
  have hc' : ((n+1-15 : ℕ) : ℝ) = (n:ℝ)+1-15 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hc'] at bound
  have strict := mul_lt_mul_of_pos_right (lt_of_lt_of_le margin'
    (show ((n:ℝ)+1)*q-30 ≤ ((n:ℝ)+1-15)*q-15 by linarith)) hA
  simpa only [card_map,card_univ,sum_map,Nat.cast_add,Nat.cast_one] using strict.trans_le bound

private theorem certBlock0 : certTree 8 0 = (366115825173126652601330299272453206604141029183860216671492818941195731064088596992519773692215830678125789028992259281169902199017264014125260350472656886422243255583918906240) := by decide +kernel
private theorem certBlock1 : certTree 8 1 = (365739754040971665564000965170135606235616661021673329333421562907597758119840397444215739591789486866268804298795763828319969947591912899567584257467920523649366712503959430272) := by decide +kernel
private theorem certBlock2 : certTree 8 2 = (365611477113445367887726343812623820425716924552302362190068139240663609991730123986033986273189657819750011916348536896066525296248910158395961715136909324686638170149483305856) := by decide +kernel
private theorem certBlock3 : certTree 8 3 = (364482698097220701480092195155574393136416363799427504468036622231995675262071519814351831614176078478331805311885321632200940386136472655201523766141443732345446997831003808896) := by decide +kernel
private theorem certBlock4 : certTree 8 4 = (364226327828836414975437684784619663349549527028559674478808685361823612140396702437952224762930318836494604295849436018135961321122966661485920043203394593253819393974164904832) := by decide +kernel
private theorem certBlock5 : certTree 8 5 = (362347560251468608283940934323083614287887815804307661343770384231561069180078142883757587957927661077188408731149008191009822690959967255446845463483281623306285888324994737280) := by decide +kernel
private theorem certBlock6 : certTree 8 6 = (361963714259615104121264740089380365193970936198972101149585561025164343557036053456788908990498521873718806228801885207804711963633216553591738156811719431451541911462869851008) := by decide +kernel
private theorem certBlock7 : certTree 8 7 = (359339484229114086442085997931710912132835124941650858801443934199460187986632201004324196241709785356481764078955167874263920542949534826381303149839180807627457232043997275264) := by decide +kernel
private theorem certBlock8 : certTree 8 8 = (358829087230844839343684475363953309947827195199717894580669090534528901440304943912693878000710154896844940848903788478297010868220728091610526740880099377241111686806437747584) := by decide +kernel
private theorem certBlock9 : certTree 8 9 = (355465716736531710392270217186545523784823547184281570467850276264795739478563187887415405641011046731938792144441005975586136222834105372591754209008764875062710979329736975488) := by decide +kernel
private theorem certBlock10 : certTree 8 10 = (354829998320844283763160308164736331362668584822695346055007435343349758837613382217018362676490381352169844701413098441559675574878644151769679387752932464849826613322780105600) := by decide +kernel
private theorem certBlock11 : certTree 8 11 = (350735590003151021945859080695387836179885308184933709601681236725401657374022643445643642752775060581054419383596971468624284097156672632132075382482030357099720940452776387712) := by decide +kernel
private theorem certBlock12 : certTree 8 12 = (349976081668804476565846001015299061050888810618901601805565358071386513304183004017445552419524669206756797146140293254266840008724070267898943131091772895951929451032288287616) := by decide +kernel
private theorem certBlock13 : certTree 8 13 = (345160499299336399853683458998139692347534706402011790342160318261236445365171641025060729143861378051070714279378620479155749610780767735500461773041840506191984417511756407936) := by decide +kernel
private theorem certBlock14 : certTree 8 14 = (344279030765342871396726306133538817604191629438119370784980182561093424394251537706735890665297059629326251687023371594095812459262272875023808174070645553345767638057361464192) := by decide +kernel
private theorem certBlock15 : certTree 8 15 = (338753875484229010650890160715031530862375722783512493055649346219011534462403209051646025053875799311502186898013355804600492373533257504599285211471512951593945947114226721920) := by decide +kernel
private theorem certBlock16 : certTree 8 16 = (337752570281907789971338386892748788037119688179292727753524859809844615704187169339723646415555997527341972613877150005346353342665421832077410759914098188078437133207649770368) := by decide +kernel
private theorem certBlock17 : certTree 8 17 = (331531152649685382336808665550074406732414547847130955264233885076401750482298727618059084035859315975643717015759234991851813304587566645154970907058534665824205987480935474304) := by decide +kernel
private theorem certBlock18 : certTree 8 18 = (330412423006898608395244034283063590140185326134101673283493571500758199930854022172343324754804663167751915387038793526660809835656556338529692529846214371313909929305319529344) := by decide +kernel
private theorem certBlock19 : certTree 8 19 = (323509730938261055233565037806178109762496363203681878811042392266756216821988512707197239551663119818667879075677779101278084761581854525598089245426290237967587319876897612928) := by decide +kernel
private theorem certBlock20 : certTree 8 20 = (322276271968155324140652803673199678954971226533409173234777012073737297428664959343781820679433691749050293624917102664206377795408833115810903653277469982298564040888406104960) := by decide +kernel
private theorem certBlock21 : certTree 8 21 = (314708934624813892764818305515660336371816917438376961011895789912966527942219901681152154431969453498901672800769601281807021441759186080793563026471645440795502639947545191552) := by decide +kernel
private theorem certBlock22 : certTree 8 22 = (313363717833067589737703363231122971272883212859140866544521318256025260190125793439951138510193671377174822736277785007866869281754423188052877105030838448925090469014711163776) := by decide +kernel
private theorem certBlock23 : certTree 8 23 = (305149965562711970507593998969102216703012868940737135468153014878976197791648842789231562376478616799950892142154316916013199430881976950768839967870854858677559738282728629376) := by decide +kernel
private theorem certBlock24 : certTree 8 24 = (303696231688929908114276087064722357898847388671286775254515116907023771756481019130773575514781261337583965480970998244821400838462258498681174377023829664627986227908528429952) := by decide +kernel
private theorem certBlock25 : certTree 8 25 = (294855852106798016070732632843769439291247341711055783398644975521182192784580110929480125812492136582199293045370574498396060102386154089522520591047682811219838611832045970560) := by decide +kernel
private theorem certBlock26 : certTree 8 26 = (293297103317299056769497665132030230587135096768157516652087376232643082400901944774952018493703394390751274429883310144693721145718726839762933524441367384258245367076821523328) := by decide +kernel
private theorem certBlock27 : certTree 8 27 = (283851393636159242436179499001760660893881107142762736154113239577311349929034335646901131013624773793250149216682625553732210749830062146248815223591049985789145866427455906944) := by decide +kernel
private theorem certBlock28 : certTree 8 28 = (282191385086965131631417664620801956252033684078384989415693872785136543558217841686593172326552651935849720148329749854921647195098864002949013288162141958260837427346074360704) := by decide +kernel
private theorem certBlock29 : certTree 8 29 = (272163100810351851268015025225314058209785052039742470836867008400941032496699435332250561863160869389391139330746674887034523131758544280952189281230677069401789658172288803968) := by decide +kernel
private theorem certBlock30 : certTree 8 30 = (270405831600702724466330302281159119717560272355963550348602170138158396325583498756313993543790990413615217796189733028627021827260245484048220053439611797796033721394041576320) := by decide +kernel
private theorem certBlock31 : certTree 8 31 = (259819131703007941927879691298829850643355406722104946454143509102075486658824652056379213908075299432873760427877815089878192925267905636811963794734246392322457754623168881792) := by decide +kernel
private theorem certBlock32 : certTree 8 32 = (257968835241198240725401181247864143075004242146349652663208789032015935310974629960626690335622019174402861440116120680438356948937320292755039064513295363375758247531684158336) := by decide +kernel
private theorem certBlock33 : certTree 8 33 = (246849223966684283053192501026054801324926575819809487853716579847120249571896003831478903027770386505272633069917091814603533772128958571786069273997032090900687058079141209216) := by decide +kernel
private theorem certBlock34 : certTree 8 34 = (244910357771428582082964732334195146430088606543436214745031397796470631414601809028909956767967320647321810394861072589483269207035111225682903043228809706990633428993235082112) := by decide +kernel
private theorem certBlock35 : certTree 8 35 = (233284623192373457306531606006074929899601836494600889153103122856989707065841551961305702802115394979619534240079477619287237897520447844980671284075059430602444704743767811200) := by decide +kernel
private theorem certBlock36 : certTree 8 36 = (231261858154271556679068797363155533020039593604634011536452709534339752363596454698063468152054535302519502885437748621605613947108543889788014349929313495178543880669827029888) := by decide +kernel
private theorem certBlock37 : certTree 8 37 = (219158007636265238418230400950709745741238626886518459578783593651659419668193806402505609523886126479861828207218607426341260248139864257507780931530355271514891581712838829184) := by decide +kernel
private theorem certBlock38 : certTree 8 38 = (217056216765236536774306868687528168390674868868031020641127839227112378062409065526932345565275310256773517695817312219557971478374265486528807210539055813786784972586436385664) := by decide +kernel
private theorem certBlock39 : certTree 8 39 = (204503409495097611252047084864287655829935816401484803338099066856130395845493877412609696628088698199253475823338702647630522387541345820756766638852134955935308437720673428608) := by decide +kernel
private theorem certBlock40 : certTree 8 40 = (202327656180893108689898040528797674106658476219574473483835183851252374798148350021918246436872512581652930272544006432754148611977830576496627948523262814762998823696291191680) := by decide +kernel
private theorem certBlock41 : certTree 8 41 = (189356132919751507199727677481244413471860602493713739891545976842730061607888914552298324614899012401542567699758287270977797693549241918985684450162403346135406964370673378432) := by decide +kernel
private theorem certBlock42 : certTree 8 42 = (187111658733824810016613063929168550996942974423022235009827466125885154722285240260741774125523714327857251282832370640599615268311356680803906694504779567525149032721612135296) := by decide +kernel
private theorem certBlock43 : certTree 8 43 = (173752668964601053843182601862280511299271957410664586296730259307483359105035239025161286687611869208767882327835495760379685921947690963903276820426448135000994646751847523456) := by decide +kernel
private theorem certBlock44 : certTree 8 44 = (171444881032724635823684726049171212094457927205381272119541157229606316586879826782104759059272955483560071575217589326457101044820809261675298613517844014934459612541013580672) := by decide +kernel
private theorem certBlock45 : certTree 8 45 = (157730607677512979653195396132654175679140660375223313799349974471579203170920086645007154277611675779284389818108126040188951966273816749248608927343149414480018327633427571840) := by decide +kernel
private theorem certBlock46 : certTree 8 46 = (155365065653560032298825027102881690966672199772611187483759654415684436534710706804044087038353317624199133898381121380731379421804710155463829817674262454638046905517121330048) := by decide +kernel
private theorem certBlock47 : certTree 8 47 = (141328547542276960540911978747927607607349360159572298246222030134876685616348941713529625359934246982693203485228718756942831568826873383801557721760549254679628572349931857024) := by decide +kernel
private theorem certBlock48 : certTree 8 48 = (138910950214549941218159514095459002932793453185777936287250556215912964734242193662012701614359747119771893217990900548204216941869034280575040187957574111321924619432443108224) := by decide +kernel
private theorem certBlock49 : certTree 8 49 = (124586002491626513888409547652813046953784790379707103512025632618614649357720866395509276147516552278706759138821887563954651211106473745604829152428828417586968306980291486848) := by decide +kernel
private theorem certBlock50 : certTree 8 50 = (122122174053998655363859807510474772627747393517048235420189573710415068507674238775569829115824559480403553121900207758009692650102103540911741195994418912898045350340335623040) := by decide +kernel
private theorem certBlock51 : certTree 8 51 = (107543306714862122620767165092591194448754654235386030982863919820726027596598017572088845847659764422176299310236292009856764288373523121999544800762236846192970815511671481472) := by decide +kernel
private theorem certBlock52 : certTree 8 52 = (105039182735805558918591665076555874995293250848681998743115215834923843466539573216627462373338419817424527165575630659387244078399657984577866030996901192931780880300228598656) := by decide +kernel
private theorem certBlock53 : certTree 8 53 = (90241517489400442890429690796282504391096395528997091359010861214111556386119372559268883525605761685295482484810573599596755509763260466091167291594001536979758089144197588096) := by decide +kernel
private theorem certBlock54 : certTree 8 54 = (87703130612702278605280627971694793429777585508131602414882023820417285183896339114863936021895619895993232566076809633467824725662351000571676700054915581567902535923214965632) := by decide +kernel
private theorem certBlock55 : certTree 8 55 = (72722316270332830619718052226000416180204721045726282495959713215833734642555217397034602254284244644439942692594344046919382839711667787043413204818603227143902784968964580480) := by decide +kernel
private theorem certBlock56 : certTree 8 56 = (70155781681946666250754262002247169681604366534121019577580943192165942875716253431250331055373719490913605226299565344035307670080309665645432448772470902251532860707948583808) := by decide +kernel
private theorem certBlock57 : certTree 8 57 = (55027908276271437924975378094153337371772764424318496979935507877135706263369576833897751314100741494602583948541409143486131054557186861704631095282531364507620215327533966464) := by decide +kernel
private theorem certBlock58 : certTree 8 58 = (52439408972314987197032800061189759230603799930696338444149617797882334805389500308294826504834130501365248549379774924248850695517207616880536978024605533343049583533411392384) := by decide +kernel
private theorem certBlock59 : certTree 8 59 = (37200920813381532751592021084038888454827514212613664912291056529566711444522415596744860995940458739062767513968882879148248266601793238837199903853217836363836935507244098688) := by decide +kernel
private theorem certBlock60 : certTree 8 60 = (34596692704769649095580269517671354366310159448005640233277504469855806076499399970261422326632809910535226310330058924517920835951771532726426727412576108416875867949947542400) := by decide +kernel
private theorem certBlock61 : certTree 8 61 = (19284300582535583228827400548221917558395865848911459582012869307549360124973090015454496795862352156942090836579570218353350632288017526397639674652074214310600876936346870912) := by decide +kernel
private theorem certBlock62 : certTree 8 62 = (16670617472131068797626383363807221246790060759962956667691741916049611764781859860504132860137964682638557575820485777676118722873948934759450896456353489384927574817171692416) := by decide +kernel
private theorem certBlock63 : certTree 8 63 = (1321210216970482113331525416649543068835239592266520267442725674568817064249004289935127240017573963546580721382860812418400005989472141782875412875896588819439206990022059136) := by decide +kernel
private theorem certBlock64 : certTree 8 64 = (-1295631314558499946939806609478157032858560964150599205911670689440660113391381490739071794547302290269455747570843271047732317089571427756511274757628681236526127837614843008) := by decide +kernel
private theorem certBlock65 : certTree 8 65 = (-16645075700322104525092219777966111215874825593875563008788151250590003003016850025085535672235786150880659008876786629502985945474956211297088736126093564720375049668593834880) := by decide +kernel
private theorem certBlock66 : certTree 8 66 = (-19258771463530139339328923438188227130518873809303384918517858763977652049104820850735412877607703206481966208891466335313031772298444188791653659478139668196255175461401928832) := by decide +kernel
private theorem certBlock67 : certTree 8 67 = (-34571274888995693588597107270765475238599799033413396197604627056939302395773499818578688311073984519562671835606596855456550174073155998089798063548253611707363864234340506496) := by decide +kernel
private theorem certBlock68 : certTree 8 68 = (-37175528273034792425288748300308349555503497391874199181420664863158022700617272616314544535789019018346173502267449130085772265260200750653227387237697355088612301993806537856) := by decide +kernel
private theorem certBlock69 : certTree 8 69 = (-52414201642421535001112905986367170766271838458246305372388143038315626033218214580561502298743636814522677518374325539665651980046689299342788354643209884415768499991642495872) := by decide +kernel
private theorem certBlock70 : certTree 8 70 = (-55002738784180712235970041036378010269316131025932921497941101980622736240873276942700425214683397678487484069496195536683620099899462429055404797845599190838808043995292378240) := by decide +kernel
private theorem certBlock71 : certTree 8 71 = (-70130870866282406908586115205459605740747185438664174177805049058989976841914656744068290923329477958331386676186150805736314793274185853567035911774083779315223853731041893248) := by decide +kernel
private theorem certBlock72 : certTree 8 72 = (-72697455764756317168082340794187168000459111231982680601554848830386287062282552183871291959332757401068322724330908817764465446059168708873606179765231741258279768035919799424) := by decide +kernel
private theorem certBlock73 : certTree 8 73 = (-87678601634110873550876160868855875224184221218756581650419736386561279608227787278086544747770709521566460177552072828532224063380256296949373315562656299121936458748063767424) := by decide +kernel
private theorem certBlock74 : certTree 8 74 = (-90217051173596037757278584255960102616934563760535317528625496292305943835115258184879295147848767298411943949045161956328447794153000921766127419235617895061207698274839045248) := by decide +kernel
private theorem certBlock75 : certTree 8 75 = (-105015120010377353701032402393232514931978192011013159149198900585894137872978753964898034500838331321284240785651029326868436394518452009423613952575759248522630047514348346240) := by decide +kernel
private theorem certBlock76 : certTree 8 76 = (-107519318856317203847365437329801099094965180364943475971006748407341748313698100520266802047121248322956608630587548243217265060666003816968907909175167588688310742298859807872) := by decide +kernel
private theorem certBlock77 : certTree 8 77 = (-122098660893521085065606325086118190475066363980024650544241999087597951894310931866651643266409310161951893690073496529385942857208986515870160908395148296906114208643117865856) := by decide +kernel
private theorem certBlock78 : certTree 8 78 = (-124562576225131698879851582940447763964975669873034381928830859548025206713294157861876639603362284383739432824522846200344513300007123748594877056311453951421575949238487098496) := by decide +kernel
private theorem certBlock79 : certTree 8 79 = (-138888068633707167532636310065926152495258765899627342771087524765731853368101203677429253699990610920430517686576946931390867161369086928729287388238793693869589174545472936832) := by decide +kernel
private theorem certBlock80 : certTree 8 80 = (-141305764677913567337045243643425535863240449498298544740712991465556957061874703968895091618042205102747650632924334090529472454857628234298856843088846482590427916133179466880) := by decide +kernel
private theorem certBlock81 : certTree 8 81 = (-155342896183080822242994638498164545249636610944541915817088358769202128509743035738279048652008419860548359068979565642152730387585421220119197348364274259388754726643137371008) := by decide +kernel
private theorem certBlock82 : certTree 8 82 = (-157708548514778319129993629627556053309090392789576694035886956167186575314952626184426757016981271865381061313743016845521479292117621970743907554341138124900400667700990452864) := by decide +kernel
private theorem certBlock83 : certTree 8 83 = (-171423502539870094335549941258757802280191990299188372241091571008333532279850477065103531220404432064987968974457040142201118492345134156474359222250856821187368338744835955584) := by decide +kernel
private theorem certBlock84 : certTree 8 84 = (-173731412114095437706014941378439369129791352080113235630924684530059560773962530337001106516086016830651595373688383636812572599912154082132079129498260301816506849657313961088) := by decide +kernel
private theorem certBlock85 : certTree 8 85 = (-187091148251853564804191335158099218974936159723791473117286168880557679345858096017936172905284746791408221076121994181892775136773301096391083959148290337095986387969543625600) := by decide +kernel
private theorem certBlock86 : certTree 8 86 = (-189335755134105510627889245839063409206142472932993151944141395866080492153435509650509276227242256634201728123720136608248317896509109558675183595443020197124972591779357533312) := by decide +kernel
private theorem certBlock87 : certTree 8 87 = (-202308088749452213480920841078151961234691173938071011250454849212986928243502839482203158150118384858353531832068366218522817448966335940890387707653729409354773529399041055616) := by decide +kernel
private theorem certBlock88 : certTree 8 88 = (-204483985511139296675443877695392246626649043079187621683678555498828595113856555794906772485731983161536199573372412506378192035612373197530986737393013465621246117310819345536) := by decide +kernel
private theorem certBlock89 : certTree 8 89 = (-217037665284015324594410598906520204578999391762080311202183052479702149494984666354945098798505909798004978285745102986644280735583431740000013159521055545761014091705458744192) := by decide +kernel
private theorem certBlock90 : certTree 8 90 = (-219139610030828707253433695481272063839701260182062627072681748504503175975732943327176408845785304163048302989644289058280462547180162722302912383951790305737420774720069051520) := by decide +kernel
private theorem certBlock91 : certTree 8 91 = (-231244393252739190166561015078969151954679166543518530690129948109170491242693894657304105714733227525588417564530698139216533062031501516740666148521962772905772285828939242368) := by decide +kernel
private theorem certBlock92 : certTree 8 92 = (-233267322254648915015466302780034252830520170938717301906888875086996441974711433814541016463430417407030789486364128748937679828433981949451927875974332472592983327712032203904) := by decide +kernel
private theorem certBlock93 : certTree 8 93 = (-244894047698073366902093164508067894983170521132394542352311211366805768628550157286122520032106334901611703713240890336501449417520139359247001306919038772333996768131917929344) := by decide +kernel
private theorem certBlock94 : certTree 8 94 = (-246833087590625504000335948535040501266903214265288968269509109522123272089221609465330484795250358964014538906524299516993334185116216931869999736666565513251859655365453030528) := by decide +kernel
private theorem certBlock95 : certTree 8 95 = (-257953745776420562268952832195221980434879801499282343459885969736110069392558196900300876851114731301910115967077912119023543251486620182768433846933310021623924911314784344960) := by decide +kernel
private theorem certBlock96 : certTree 8 96 = (-259804225304068811245422060720629245477309153192550333803857025796081886605884971625493959670411533850460482384373762508306848272252673970860505788325678153354310475523134465152) := by decide +kernel
private theorem certBlock97 : certTree 8 97 = (-270392025998410296613290450762386645996345820588985476425349874592873463424591466208336624736311308511728500607457311110181288810447403555247334705481647753394115939916065659776) := by decide +kernel
private theorem certBlock98 : certTree 8 98 = (-272149487271746709559251059335211013306655809133451911674673299151433407541672936595906335462558841496919749573494926155840226970301975713737581407188948089774671745317008974976) := by decide +kernel
private theorem certBlock99 : certTree 8 99 = (-282178924051010085248037589809305064051991616971339500263479376884483751983170291846575348413036215720073846263040161178542771418965063945252932771322442749511009994742614317952) := by decide +kernel
private theorem certBlock100 : certTree 8 100 = (-283839133290963732533104301358520226536728651309515745719550535811592470240271001367177844405347512711315067474554405145924082740011089418952433514816038487817709515637660460160) := by decide +kernel
private theorem certBlock101 : certTree 8 101 = (-293286045020217228419574832314566483350091910416785338047007783309397792385137484887691790349815175466205879967774642076103104120722088610056909198076059752134804427441740307328) := by decide +kernel
private theorem certBlock102 : certTree 8 102 = (-294845002763564795257862187383159287396228029585087385456926669975607347706769408391388846742386308383196295904196804813780249302052513994466309427681762315249456988059628348544) := by decide +kernel
private theorem certBlock103 : certTree 8 103 = (-303686631842035165414072473434208935110553866538598006148711488683651323388273858408969934457291705140620016336369166266669133841803143617786570399029573801947643888963316472704) := by decide +kernel
private theorem certBlock104 : certTree 8 104 = (-305140582583911540254324052726960517964755615601928661818095007772336390995728577977840855843033046731313664131122216766964379879906395014858804203433832271683094141215770813568) := by decide +kernel
private theorem certBlock105 : certTree 8 105 = (-313355629818866194477452071082303942799334215472630579814325711987214110919025940588759032087798840507635886463972344478954972065145463451940182031495003852619700017048851176320) := by decide +kernel
private theorem certBlock106 : certTree 8 106 = (-314701071069373953572784522488231019044496958036315136224575859794595830361653579243567297601458068581655933889032318137793512972625995916391171729598202408919409727785560843392) := by decide +kernel
private theorem certBlock107 : certTree 8 107 = (-322269747048332437227299751598877035172970718219848625053623248378451590325562553818865782656065028237743038463685915287401043442324176678829058884220331120951762172043075902336) := by decide +kernel
private theorem certBlock108 : certTree 8 108 = (-323503437781824587640561363122339309775227433409588001338516752505227429319855895319880049890221901641841211811474461141240587577512389179485325988944972400653277144449902322816) := by decide +kernel
private theorem certBlock109 : certTree 8 109 = (-330407510621854426333698905423282101622656005875994111673991778027743427475673870016389246016717903535208769792058990349351664628147705617170172823125201627447171253760972938112) := by decide +kernel
private theorem certBlock110 : certTree 8 110 = (-331526479099002689348854444708340366581474155231628656426770753909120572839368274591932001993951879344588547837165787284323536100863564207769789425905719406543825862642981020800) := by decide +kernel
private theorem certBlock111 : certTree 8 111 = (-337749318461056890533316301789770649942412050528945928612823704240954893619805694646826268003788132255170260090906420087397554642004851494292742878037242834232810873803542485888) := by decide +kernel
private theorem certBlock112 : certTree 8 112 = (-338750869405416060415511271711132831942135835791723870192218617116677278438948435839665432620517545395805368315121357335553016445807320157424796067563349670495127816468777542784) := by decide +kernel
private theorem certBlock113 : certTree 8 113 = (-344277486671219706537594589767859543335115592115872678489551610960668286776483427142302705220564593681604179065149611105596410982742399237028835185039967015860566456803837729664) := by decide +kernel
private theorem certBlock114 : certTree 8 114 = (-345159207783655124425010030464676608479673721509595090214496099653355549070207828442871783965798342012058110908018188779056516351926388260138225298012025397377491863573906990208) := by decide +kernel
private theorem certBlock115 : certTree 8 115 = (-349976292302534482261293917264141074295889639369501757915634052262476866229475013315520853534856485247891138134846163995599217983008143131121577794873925452253404205875516791680) := by decide +kernel
private theorem certBlock116 : certTree 8 116 = (-350736060098592411683287029913568168421331706084229731314285741388686374406033009101138355336458484502013525639993537414369356007586958098353871810947958052241848301546481788032) := by decide +kernel
private theorem certBlock117 : certTree 8 117 = (-354832011421850293596555026502089642710146834556225742474079558452797850622550577840149719594922997970085161236926764063062073033494283551499810484867880973956406257166220647296) := by decide +kernel
private theorem certBlock118 : certTree 8 118 = (-355467996378918059648159395093393124450826484834837574552964558981160063778112623146608613361794585976543064361097278457775159240587419647790410082839003607710304993246330365056) := by decide +kernel
private theorem certBlock119 : certTree 8 119 = (-358832952409882925150375410326675899800660076404674192294483122152568557864707042951419400595421127122733890551795016081802608341598088447410651596237459790935994472662322764672) := by decide +kernel
private theorem certBlock120 : certTree 8 120 = (-359343623412805294532731694534060811189217225105678559581924892797340357566024767512022588408545889918853520183319912309538530170737032864014885931272633689771739249919170061440) := by decide +kernel
private theorem certBlock121 : certTree 8 121 = (-361969484411508704194001467883148648159264048994642612820092188219227615320113383337732833871990923731982849085230029073265700674093667346275640066530558102855651837421952818048) := by decide +kernel
private theorem certBlock122 : certTree 8 122 = (-362353612487197501138586617459438631438883019491781245229053656668052598811761251077187360551211742010873156834683620030892728886873736491528619508070198418698239241041197802624) := by decide +kernel
private theorem certBlock123 : certTree 8 123 = (-364234060879755938027780203752772760821784872574537206776563248577858823084031795548859618699147970309789441199205969669716860409890623558785858403751635214523330584541183204224) := by decide +kernel
private theorem certBlock124 : certTree 8 124 = (-364490722213249856416086490751645276483702164095271092549266858817100436706138994552468752727418120997140429410662471570713552034788402488865368141298225229723830511744130360448) := by decide +kernel
private theorem certBlock125 : certTree 8 125 = (-365621238167434678975014653803316953367965853712002471548541632755746530229451337398454618978117529936403085373013644823220160013962371681431492501887813046994777870560761863040) := by decide +kernel
private theorem certBlock126 : certTree 8 126 = (-365749816393834421612825277709190309469134128995028752981328405997044910131706576820177880216891174364584855792652023373241984499602164466433102733632341059848127586339081299072) := by decide +kernel
private theorem certBlock127 : certTree 8 127 = (-366127689134001216775056225211085168214363025404098460116109622228443334168706179772460416379721705992116210457914983516019972560526933436960975612281853968614511116449169398656) := by decide +kernel
private theorem certBlock128 : certTree 8 128 = (-366127815400294156198589711270863853950640332713424106000190003532741856780130685493147044274523776145781490206067442184076798769730348155905636726228259917676775500016958186624) := by decide +kernel
private theorem certBlock129 : certTree 8 129 = (-365751414133724863024953449117792488199526348490603041355897128627133963065110862242007977110996235442575226906606891602931013549261059354913073191502259040014895744375176420224) := by decide +kernel
private theorem certBlock130 : certTree 8 130 = (-365623086471150689132586454346923169897283305768004397223305055454884328750515248385506393390909973381547232126629185088597018228227156352877143913499075797856291263215312184448) := by decide +kernel
private theorem certBlock131 : certTree 8 131 = (-364494038471480624054721024468432620593836498376448871438163819593925116933001598062157929720691760125189425899323428748179342737651215463913446905469141013651217988453046279040) := by decide +kernel
private theorem certBlock132 : certTree 8 132 = (-364237626799945342083747244898194624308488798744147448310479318830588596436830039387789811011913556099577873390652999151539526854977250543797766140715303476838037021288975443072) := by decide +kernel
private theorem certBlock133 : certTree 8 133 = (-362358639301224419151966032702998793949949524717627943699544061880769709404684240740610964331613556094725041069733615967726498222788935240565417852662997328683158261783609334656) := by decide +kernel
private theorem certBlock134 : certTree 8 134 = (-361974759383371096337117953814009932543606679117959607637016539642279068338347391397793760154397525305997144880693612268648380313912971201800721532852513409967909777649466221696) := by decide +kernel
private theorem certBlock135 : certTree 8 135 = (-359350348694152338537587823611121306057060297957930128744731207671668145014016604525948742793171294112562004348424871954503119812040077762051680163526466255918396196874594933632) := by decide +kernel
private theorem certBlock136 : certTree 8 136 = (-358839923746451295619699907050822829473497199823871206914667530029524698079523962275084154472775610079318679556357506926284682663653378268471373877827762108363891584085709694080) := by decide +kernel
private theorem certBlock137 : certTree 8 137 = (-355476403943201530173176131681723468890366526170905961780072158663589574334736771755475627747265466896537167349700602576580365055528112829497679481075243767724685506641807399808) := by decide +kernel
private theorem certBlock138 : certTree 8 138 = (-354840662345433654636602138668572550434326566013609019949820244109877065747587284628006328632421103802435605204865262666296864376283144664058505950264774597601667678428644648064) := by decide +kernel
private theorem certBlock139 : certTree 8 139 = (-350746129705262824576141680976521403242955202633090024901254728519515114929868521738344333685421115614451941820775750757868768106082254287593782119480067362224780637112323136384) := by decide +kernel
private theorem certBlock140 : certTree 8 140 = (-349986601985869279381459595500946056135129294361103872598647487382392241366373505940822584614835106890126913484483068293445254031265181978747164563330366406460965416667876828288) := by decide +kernel
private theorem certBlock141 : certTree 8 141 = (-345170915185384005274513501092112999205854289297893996533439385784657412341655948745745594239499170368506100920251380091973045525192344951894870697945240246592577450920073878400) := by decide +kernel
private theorem certBlock142 : certTree 8 142 = (-344289430288253311570568996348788003601693415402739474278714388635210980793226995909312999508515211295248364249878229552205509097891650937162542622277135706510655515264964240512) := by decide +kernel
private theorem certBlock143 : certTree 8 143 = (-338764186407028383084280518102912567639442901819875453873170566417984930904761378956765600484344883739073601774345060056153158547626821207469743761832158625256918142499645676416) := by decide +kernel
private theorem certBlock144 : certTree 8 144 = (-337762867247260119121724042570208363241703135450985700041007136421339712943774176500526766305421968706854020505457439326122253553988332400422346978474320232481610034280275780736) := by decide +kernel
private theorem certBlock145 : certTree 8 145 = (-331541373625829897198681930980030797854300447710451943828389186614547809902981351453844763471610400929230316838210933475143535123736776060238268464128845529215433020464459012992) := by decide +kernel
private theorem certBlock146 : certTree 8 146 = (-330422631943934316248114843897251469325190388190833039218246880942812644426421460678951604486986326390547998884195860382061582315267653930503940543615110288636883306542141678720) := by decide +kernel
private theorem certBlock147 : certTree 8 147 = (-323519873957327996401369534664720125202521155523032203547092200670128063606041842945000149870372596017696167090699219738761712829276490762655666174603879672276439120646703799168) := by decide +kernel
private theorem certBlock148 : certTree 8 148 = (-322286404483191482218712951439109217769432161209214804122425818354214540877686260402979753341500326778334126005117372098131784529222572115390198336550071472819281697343301887104) := by decide +kernel
private theorem certBlock149 : certTree 8 149 = (-314719009301863876384451681128049279845862475747152360833848421591428463466933072733508791858151534903154912138371787449738819220965725114242113708449125094685487505714869558144) := by decide +kernel
private theorem certBlock150 : certTree 8 150 = (-313373783241629870906090851602153269592928622490661006591586591132548902045276620573579195257423297867043569483794732401580040715889797173235675926135420625030374364850329625728) := by decide +kernel
private theorem certBlock151 : certTree 8 151 = (-305159979662163719995816617969420159126537289445878841998879295354823925403423388395478490136283079377013713838641562861933621678101914033543339398168724018911554762411613477760) := by decide +kernel
private theorem certBlock152 : certTree 8 152 = (-303706237522945937797137460314502076345316826494122697248820808012737838936339203900886579732712984868859485939787605909866552564232447419641970794890038913979086719999592244352) := by decide +kernel
private theorem certBlock153 : certTree 8 153 = (-294865811961112700736608380735951745183325476540330536279006389998477169183278504303463450392772767560873869986479207059521613116810654402655681152400001960290005626340833352576) := by decide +kernel
private theorem certBlock154 : certTree 8 154 = (-293307055730170299438617342821819136860184179850862721023741080765823589138010390582406537609360945241984773922536730912622744412489290220743429428121686550731068476979030402176) := by decide +kernel
private theorem certBlock155 : certTree 8 155 = (-283861304478822998994567271630162304552348421325753069585262561453551986784802482349583464619757519955560500660786441954395645654592676362563000466388132332642104354386712058752) := by decide +kernel
private theorem certBlock156 : certTree 8 156 = (-282201289175483991422886094388773754584113649463663489925530919803779199313701648888179190405596968352543059726740841248816450920172375623196513746022586533265694668498488927360) := by decide +kernel
private theorem certBlock157 : certTree 8 157 = (-272172967039306507173564074814083014313365581169320121951394440925866967138069108085478405422614332209363275600162843571598396145284085939224785939537888389246241571806996192128) := by decide +kernel
private theorem certBlock158 : certTree 8 158 = (-270415691659524069828935136328956747608181853003489795610923358076904779356203821430024223195330052314008321542679898079527811029668079129147144142016737876504226600959845999744) := by decide +kernel
private theorem certBlock159 : certTree 8 159 = (-259828957087864235598133114437606668639326341756919074555723126684641811584610018729218162435904862886072739895319273341732406503207613759946507643022768882074975187949795269504) := by decide +kernel
private theorem certBlock160 : certTree 8 160 = (-257978654962828607613442678957643449059748582307876491486830398589101235956588154408526498982601945462389877157380381739304045309786775893552758268931062616914753036181322736768) := by decide +kernel
private theorem certBlock161 : certTree 8 161 = (-246859011810685228676963131813802986100109141173545452689104394394914765494204174205247824816936667420105733943530694391435237157706793987276746521369260374971631129701965749120) := by decide +kernel
private theorem certBlock162 : certTree 8 162 = (-244920140402389477425833923558144066275283286122471083617296533882060855591958713085822334130866534025202579836875502291623561364712235330094762920919607259614190404971372094592) := by decide +kernel
private theorem certBlock163 : certTree 8 163 = (-233294376458093356990980474674726386662508194305739665194990173072289320716651484704393133430875154799374927153644900589640984788581688062203899717371629322360521214195723787136) := by decide +kernel
private theorem certBlock164 : certTree 8 164 = (-231271606616162258098576759672037182901861922795455316648444208110465866601683317946454397696514601751767018177708447163231922885221723548892665750773667343680758693531523622016) := by decide +kernel
private theorem certBlock165 : certTree 8 165 = (-219167729042375859899891752095823536418212556573085957241699633711190551921092637091393400914405158355424156984357390948033886305203271988278511212226681113237571045215249750912) := by decide +kernel
private theorem certBlock166 : certTree 8 166 = (-217065933747811345155910801977533309892802962415259639386285030141989341135236855707349448670306410405209642045450453464156261259128491585069128280413910918246084801686178768000) := by decide +kernel
private theorem certBlock167 : certTree 8 167 = (-204513101590158211486785799252750180948996889641990115772688115126450016711061189853626008209990805976067414892842243513328455753818099096707964322050020401982539660130344098688) := by decide +kernel
private theorem certBlock168 : certTree 8 168 = (-202337344212930140370131090713799210944455205304742598716628551884213888914106267888311044457581850144537226441160322186450643421685363312539362097499171664663544406810328441984) := by decide +kernel
private theorem certBlock169 : certTree 8 169 = (-189365798137841185456409482027013066505243992312594072961137132054065097923333996430018915044177528238950820632182824926648177139944820879711982565952441248463038480241759214464) := by decide +kernel
private theorem certBlock170 : certTree 8 170 = (-187121320236456493824911437796270556516855660239423549265943191336694822657600984202928043480325590978942784208059910066869591642110497341029990319206976644180951608699353441408) := by decide +kernel
private theorem certBlock171 : certTree 8 171 = (-173762309666673623917464917684391372165289811691132510626791346370146387475547871538239929884295657280533209942873410720394383938212998536191502740124960777291868174058103364480) := by decide +kernel
private theorem certBlock172 : certTree 8 172 = (-171454518358988150888688134527401592894268868333530465038883319734788716329261743380600791982975104188292325597289325592870656686717859336030447840511138543450299981185211311232) := by decide +kernel
private theorem certBlock173 : certTree 8 173 = (-157740226181584519176184366219215147308597184661550566922803426286244148291704282882254738439737100216997068065675639790934855079228944139588047163927940703334636675304213044096) := by decide +kernel
private theorem certBlock174 : certTree 8 174 = (-155374681117178035902460384387095260610566246482673441695057140865087502623904512105803588268603040801252368918747103271303256133704702722795501741350428665783676961709453616256) := by decide +kernel
private theorem certBlock175 : certTree 8 175 = (-141338146144927283223586788340348018944175177212006731549157680013893532132255155997798445277400138020777970612275178267884684966765276418205743602304555538232409232055802649472) := by decide +kernel
private theorem certBlock176 : certTree 8 176 = (-138920546110341557907036573766663247412771995129278480243166089035361549659385957987216999129199910982217062132583918457876036611983416703158960965109494121477417500895070528640) := by decide +kernel
private theorem certBlock177 : certTree 8 177 = (-124595583482784834929348016443628456165461870609746444845535353996793649251584251886990734897771153106948841929348203968674038249636365314391690780888069827147628920003292158848) := by decide +kernel
private theorem certBlock178 : certTree 8 178 = (-122131752671825181450253927126726815956813716555043314365821166779532006313870770431252316666183752846534766564114441865712078755676915497919902736297963915450385899880640029824) := by decide +kernel
private theorem certBlock179 : certTree 8 179 = (-107552872387434446551368923644561227382220002692987445529236491409400271926162052265540155212722504650386321346872795376360882454926798623639712331380640884668649783603595697024) := by decide +kernel
private theorem certBlock180 : certTree 8 180 = (-105048746369555448940201427146745993463506561922528087800705317317847305092086419997547380012899564414610872279633784524086679832614653050049179525663139569276033998122668139648) := by decide +kernel
private theorem certBlock181 : certTree 8 181 = (-90251070144965052203497154744668492638776479922732628560617413370645188682360966794640061734945266931631136064124546578085011899147388638514644073251828829225457525744886995840) := by decide +kernel
private theorem certBlock182 : certTree 8 182 = (-87712681565499490627951957421458886636279048183397555317017082896431021568513505901787805968960297393600580519414495180148866251690303720811154402174943372205767295730876294272) := by decide +kernel
private theorem certBlock183 : certTree 8 183 = (-72731858221866732504527943958674547025240389060365487036343897742385731241197412767630046077788277078732004391221036353356178858383247443769960753691975122304286596691397827456) := by decide +kernel
private theorem certBlock184 : certTree 8 184 = (-70165322268511753762654217680234683625271428759124946161687076129897599242099136596168347950417274431177433238870052603550683976057234750674414425394415106682278332251287200896) := by decide +kernel
private theorem certBlock185 : certTree 8 185 = (-55037441848663134886836475380480005178000775331736512065786307543995110924134807949626894171524159938996843387639014473549959518014479892277503964913939761226197202219792194432) := by decide +kernel
private theorem certBlock186 : certTree 8 186 = (-52448941519208155628699945858542482172388606289512050297290967595109181388730618889849179336656428214045657198091850975771808955323159360787828181299536606663107003138639537280) := by decide +kernel
private theorem certBlock187 : certTree 8 187 = (-37210448342324500190130929099395783963309547993837134569927928817073326781572183886527390607113873537653890909699778064839757874622809345471326774862318286987031694635046132608) := by decide +kernel
private theorem certBlock188 : certTree 8 188 = (-34606219549090106197674940369421220123387510635828455127149511998218299966900676386468976607770147271807761329287865314994945579089469577339478951577600562932647529906894939264) := by decide +kernel
private theorem certBlock189 : certTree 8 189 = (-19293824412274684752117287751633729751320831674257910152370764481076464308295158498615893354253049410263502416759698681041402502139962685536368944755487984717307513619290381184) := by decide +kernel
private theorem certBlock190 : certTree 8 190 = (-16680140959129962697719187692402857259301786821520249931122755440017265411896470504879229141342309781729449608823673847015703078056979979403682071668199086201612459081646351488) := by decide +kernel
private theorem certBlock191 : certTree 8 191 = (-1330732697284197689859666756151786976933497257707400560805005898138843564761139049198263348504551924302829864991868109363981706599324431397816558139609278462468148015081315200) := by decide +kernel
private theorem certBlock192 : certTree 8 192 = (1286108834579251623319627226247727653554210493510937670306533257220949633081550604326189126168199626315179348360575377883402135147125733748857765446329009699060089327023676288) := by decide +kernel
private theorem certBlock193 : certTree 8 193 = (16635552217581870099306999054980810692726445157996068890527319119277204204249158929043547369777421160896094605522986917016951642970996431620731870983511034937596472103848518784) := by decide +kernel
private theorem certBlock194 : certTree 8 194 = (19249247638718114702609841492902911938515329565974205454904004950334780561934186834045998229529950265822873661686063185659703322709148204094782435984169599298796205783756168064) := by decide +kernel
private theorem certBlock195 : certTree 8 195 = (34561748053520500265559472030081486845580059302236731482729500893394653787342275024610290802930277883340033151665298104626869088503631122986132707935213283117464683042293294208) := by decide +kernel
private theorem certBlock196 : certTree 8 196 = (37166000753603993463366590174006275080983469260745302023280076331072147827325382941036331206581933648828103655743409302639752388084214853905730972449364290447722909916838878080) := by decide +kernel
private theorem certBlock197 : certTree 8 197 = (52404669108947169054448346943650635933389596990763071442993713185491399811481108612561906685311538826160749888982195876989106218314843838375045996240201366887280606950271100032) := by decide +kernel
private theorem certBlock198 : certTree 8 198 = (54993205225872333000163758921884007836323969174902507766125227823044969021599040567322444871802677736821523295053491063001086706368355279946061848613314936003145014213305293696) := by decide +kernel
private theorem certBlock199 : certTree 8 199 = (70121330297691123853565945239679763100475683386453325769431560120169966982411924557485435733978469604430462560593269977063974526863907849401935610806907361926497720131763709056) := by decide +kernel
private theorem certBlock200 : certTree 8 200 = (72687913831857677690685794852936157018585859093696475149558824690498973301537517683298500189370273270141000986728992713951904769939604910459087542987373151398154702972335283072) := by decide +kernel
private theorem certBlock201 : certTree 8 201 = (87669050703820194783605752095655782633818856082776176963539542006924798611139869332930005511309868257204813015461245162954861392571850644534924358286104119605996861473429005440) := by decide +kernel
private theorem certBlock202 : certTree 8 202 = (90207498541196010227077230948401454839042568249839436607769635281287825256356224705554587607348951602328223516713208702567369080655573434744658042746478017785043389343532440448) := by decide +kernel
private theorem certBlock203 : certTree 8 203 = (105005556403643251175489111769280650753627872898884402335536042209163802320836016344369732448630678467982706110144138663803068320664158148214051596543949491903714354896780010624) := by decide +kernel
private theorem certBlock204 : certTree 8 204 = (107509753211415401572192956061332287708722095478336088586058483144746906695386053434744889278219634442428038937013857789985935546938119857889026458966566716800013685109400394624) := by decide +kernel
private theorem certBlock205 : certTree 8 205 = (122089082307198455773693360522690202523491801250398788641987073380593104774105517592498506561607730427434538171131909578981492863526334109185096214281878707494230638316002616448) := by decide +kernel
private theorem certBlock206 : certTree 8 206 = (124552995266129402034295283349623229969391538029336772667867042748452848249441526434977241708872198393226931980974407070745883083229402944505749102429157871321272859481505389440) := by decide +kernel
private theorem certBlock207 : certTree 8 207 = (138878472773893531891433564724705117529651028522150490951655227870317970148869630938213989065731934478639689483831164600402175778118828817650898477748624103423762231332883539072) := by decide +kernel
private theorem certBlock208 : certTree 8 208 = (141296166111892276626078425824841808504929500427176138595268036264110358006765319333267875892905662023513199918319710140495569101436445161415037693621227475474766014731527773056) := by decide +kernel
private theorem certBlock209 : certTree 8 209 = (155333280759914372306730919924597677728931053615149085329504102641586829450384580457526215231249057532257959248488641824524684687345087366593309479239439184157652038476430189696) := by decide +kernel
private theorem certBlock210 : certTree 8 210 = (157698930051810928555074448021371861919759198764851322753991203008141720157318470120390880379570757100916609889979425269985371476132392266892944271960715855129978591549559004032) := by decide +kernel
private theorem certBlock211 : certTree 8 211 = (171413865258553144854885250838320576968742693050549426515433490726732532954683700289003435140636600919795119090001331940252371185186483332553838580944693759652539909150823294080) := by decide +kernel
private theorem certBlock212 : certTree 8 212 = (173721771457627625556342872918502079167301966376404658142475870084531865020896438221667276927523865852543414974688719568328419940047618553000289744427656092875322704356322958208) := by decide +kernel
private theorem certBlock213 : certTree 8 213 = (187081486798717887791557230709383155203087969085772037296712767942229763985786743194972958894599062945320283519351822584552108743581112752515709226084020215488441010716362024064) := by decide +kernel
private theorem certBlock214 : certTree 8 214 = (189326089966181546816083014347043120247355507758612570634606497300109815879736316165352029457035013970513226249506771717829868314352538297708891690266895538004636900038488742784) := by decide +kernel
private theorem certBlock215 : certTree 8 215 = (202298400771562388222370479604764188017312690857489648626423144274057530250855872270784190224384639864465416199327192820905922319154514324888144691257805989364567241482505692288) := by decide +kernel
private theorem certBlock216 : certTree 8 216 = (204474293470915458486604057186557819739020804939295790396098903169748876770030570544796803148381434012321584452155719264961614657445615945894360006899900469758594088991932668800) := by decide +kernel
private theorem certBlock217 : certTree 8 217 = (217027948360406517465804537585782425825657069269259366725254675905462547839140467175434356409775905413539238119280426285258411835229457626593390390722643273202284342000146064512) := by decide +kernel
private theorem certBlock218 : certTree 8 218 = (219129888684404929270267307498452572099109121655858145026148234324058143602234141321299762772528731287530615753933185858326262242343976692591377558475487069830781469533884242816) := by decide +kernel
private theorem certBlock219 : certTree 8 219 = (231234644854890466014344201114956547300937377383607528742776018426414303450888778245218100905246760229643849918791722015445988486947263802076200932007413656850356284958613316736) := by decide +kernel
private theorem certBlock220 : certTree 8 220 = (233257569053738533375206970285666842152564603491309371134949520208712759540949232882434540181355949339709485242338474800741201585543572489927333858619651839276933382276141931392) := by decide +kernel
private theorem certBlock221 : certTree 8 221 = (244884265136607500901731122283057088375872592420173562721284258312639346883543353597005810898339744116210422385348335316434249996292954969882357205615241341782158841116528878720) := by decide +kernel
private theorem certBlock222 : certTree 8 222 = (246823299816954294738209745267083910126648318238096168162735314607724308568996800878711109938344531568347431062884849178130753296182775238062668989913255797393979290209153309568) := by decide +kernel
private theorem certBlock223 : certTree 8 223 = (257943926130273727633154391112653977157960472786820389327004929867342761410531400210369584154739837735599359686487700758393058555937559088146112390751520273996562756715735295104) := by decide +kernel
private theorem certBlock224 : certTree 8 224 = (259794399995624791544252487740284209989564849214472269354996283446239136088247750303497492851511221078477106009118665059111505595119958083472275631958927583450309686630439836544) := by decide +kernel
private theorem certBlock225 : certTree 8 225 = (270382166021803423225804389228893892096685629988118895089171377399560860830479139899131920612394767032096148083003634825035937144050745626472798573374036861054760800206657561728) := by decide +kernel
private theorem certBlock226 : certTree 8 226 = (272139621126064234634820907481014061099505179356838234507263748134100362619295097718880329158262625530043719905515486399256012979593010367858539426865483100966769551224341388160) := by decide +kernel
private theorem certBlock227 : certTree 8 227 = (282169020052447176931361058191234400317702254758677075585241547315896278491653050523756488120656673997074618107217731052702700330728251421274939438580483554697437233076848436352) := by decide +kernel
private theorem certBlock228 : certTree 8 228 = (283829222539487648673302792871824386432073713079242409538059201980612184227647713061958183199535014382505484992708326899005364404677049423398534882425420237487838515709927086976) := by decide +kernel
private theorem certBlock229 : certTree 8 229 = (293276092706398546380304140075123896343094900465964138689552570070321390949560123747601755187469610160952247722430508160543629938132014218443369120719288599380228809118361986176) := by decide +kernel
private theorem certBlock230 : certTree 8 230 = (294835043009766073248491243030670864700505079208162980869594385371133733562823236325468478870139303884106908969856785234840334655416661991587266966989302276364978735851732065152) := by decide +kernel
private theorem certBlock231 : certTree 8 231 = (303676626117963322998938075696484008030187504956828323817479004591953908372649806063800596144036522186966630294915870509951582616095092343466235760432935481977486607386005087360) := by decide +kernel
private theorem certBlock232 : certTree 8 232 = (305130568596172419629401919922620168895268562811682610066473775712146319343564924647759324161268968156873079994612240553657964082741452641811506968667659671587417069375802694528) := by decide +kernel
private theorem certBlock233 : certTree 8 233 = (313345564533492860093829332171133315509848483763439065634341718116234817050620124292827140545576013276307376915976629587079327930028335193935871416048039840480910481016759919744) := by decide +kernel
private theorem certBlock234 : certTree 8 234 = (314690996517679176510016219765016686472133932545442505027942033687522467872259158674733017229863731946996539196556825012751591634533592279858540329731976599561165173892783659904) := by decide +kernel
private theorem certBlock235 : certTree 8 235 = (322259614672787302422100022185977973862791033680861800600763643093127903553022635956937307860247165269939430196518185839270203416648125825147204820107268794524670684525542384768) := by decide +kernel
private theorem certBlock236 : certTree 8 236 = (323493294904929465033719686835120819548405211265660112718419965768231581682969968458330738649838193679574637951409004185033468313800620395838394705390434033412113078633416219520) := by decide +kernel
private theorem certBlock237 : certTree 8 237 = (330397301844553065728404272161806193986213308931680893956480561920456039720113956657064883298901204205442760549403662998482615091822054781439319847847570439676568505659039294592) := by decide +kernel
private theorem certBlock238 : certTree 8 238 = (331516258285933963587003677386950398624631582764683333301290353847470212754242194995381507537788849863717178760056282322968581061463241750380750203589342699141643156409865329536) := by decide +kernel
private theorem certBlock239 : certTree 8 239 = (337739021680727747371626886283674809079877970485756623341453716008603969309279095838425871916954682342316334321152680406846908248341528621807801121966440361242295126934493734016) := by decide +kernel
private theorem certBlock240 : certTree 8 240 = (338740558671824028736672741127540659255492323344837613263663708979415634844957169734883829836568739237279516430877478102049330686929607096605289182055505717756038283434724285312) := by decide +kernel
private theorem certBlock241 : certTree 8 241 = (344267087365040160724775783391235112670173627070970518433346125125237863320099893375644148247009339264630106700032955829539648018652949173991014464145108261123062495340727248000) := by decide +kernel
private theorem certBlock242 : certTree 8 242 = (345148792119591168345498464510881243507066981801196058113932697422451371180589186507916218491784108647520077278132930570986194414745318528770825147487915023509523909612487433088) := by decide +kernel
private theorem certBlock243 : certTree 8 243 = (349965772242027948631553284211157082404171788877154848439997772523434459572397267135170217844634923746563057943673127056297923748370786078585978263319846208079974536355839353984) := by decide +kernel
private theorem certBlock244 : certTree 8 244 = (350725520659639339371556856081427176155192661116035459077324108280325977297389347865555532356443489061293104184014283005974709098044544669675288519199584484762461294753577556864) := by decide +kernel
private theorem certBlock245 : certTree 8 245 = (354821347703864094131220752346167336046113969092728073552399058124134156862134105209635646639268480814183707434792961952835148192363056307994583181538969642259639328897497441408) := by decide +kernel
private theorem certBlock246 : certTree 8 246 = (355457309487143095373168240741044519963869584342544825758942453136416672522830255743089461060786608823977430409608743803285219686480843464573384677143704408135806597339121834880) := by decide +kernel
private theorem certBlock247 : certTree 8 247 = (358822116263719799185267813752641892109278298443634512155434827330216543447109297584600761240732705409434020926351243327757574378848421021683015115581814343576159057119370159232) := by decide +kernel
private theorem certBlock248 : certTree 8 248 = (359332759327614495805820675408899781452322569931809535843699938183107607012088106448548649290546233537136581017224089275374872875644034347841660199054316575150924174330900634496) := by decide +kernel
private theorem certBlock249 : certTree 8 249 = (361958439735987237960857763434831888664404037761041586433346208154626929367063340712966961818318208431426364409816395009857734293085482842084882934541450501108247527921938736256) := by decide +kernel
private theorem certBlock250 : certTree 8 250 = (362342533898707423265034955255719406678131427683005114603911812530595800056453204353948739983992672530255421489821850387190321050975860924861605876003712040393134440710996351872) := by decide +kernel
private theorem certBlock251 : certTree 8 251 = (364222762455473674436427695453360952810758122512736844449493423152617067718643379271288208030122391171537189212853504476375242935612318451330074461898928965256367056438970688640) := by decide +kernel
private theorem certBlock252 : certTree 8 252 = (364479382402101528453701271922271478766499976201561051024580150592303995341218138634243993040928117114732332191732788669687996056853750306494295428482440270734877880294756965248) := by decide +kernel
private theorem certBlock253 : certTree 8 253 = (365609629479629966418332848458799323774285619216359135103455581264827486006477489681804735912637005660599573999165833162581259953099444580986474398211894138384526579542224413824) := by decide +kernel
private theorem certBlock254 : certTree 8 254 = (365738156991280975913618480693192027307056658548514441824188404777777816443489989812914970995307289405429162003244265898433242563078672782960786553366234989553015635345502231424) := by decide +kernel
private theorem certBlock255 : certTree 8 255 = (366115699729962767239238741914567153376756209981156072081240792667546220265145994318002357828301786532462924401258849440077334534924571636304783360140454800650168597919617131648) := by decide +kernel

private theorem certLevel9_0 : certTree 9 0 = (73216771825378695740631461174751242114563291578014866249551352435667980672765500006182786158735918290823589065385111433535531591529221833877571576513450859117309749884424470156544) := by
  change 183 * certTree 8 0 + 17 * certTree 8 1 = _
  rw [certBlock0, certBlock1]
  norm_num
private theorem certLevel9_1 : certTree 9 1 = (72915728862719959624948219558284718891201382292684373474881860235546489942818500233788962952038446544470470574652938985925903020699205968594610198361211661538889649495614913227520) := by
  change 17 * certTree 8 2 + 183 * certTree 8 3 = _
  rw [certBlock2, certBlock3]
  norm_num
private theorem certLevel9_2 : certTree 9 2 = (72813326516952030281332092199077819835861656314899650672466085953150259197753924975169136126901018585390715534569979930566047907511822342394519740785436998161655809198797088118016) := by
  change 183 * certTree 8 4 + 17 * certTree 8 5 = _
  rw [certBlock4, certBlock5]
  norm_num
private theorem certLevel9_3 : certTree 9 3 = (71912508756341334588963238203022563128606333779704632880207194495929008242023305692556739365071365592089382532338427769522977562741529554638838025086369318130500885958920288840448) := by
  change 17 * certTree 8 6 + 183 * certTree 8 7 = _
  rw [certBlock6, certBlock7]
  norm_num
private theorem certLevel9_4 : certTree 9 4 = (71708640147765644676562852683774729624794377023681161406215898264320316534711378930109041570027146140565583641804890393113317304672573032098786215134207188911189525334183636391168) := by
  change 183 * certTree 8 8 + 17 * certTree 8 9 = _
  rw [certBlock8, certBlock9]
  norm_num
private theorem certLevel9_5 : certTree 9 5 = (70216722942030989840065937006056491654084377339828689740042792721585449199685571248242098789258172569319846107122268452264758474552608042260254344586011407251695984529345340746496) := by
  change 17 * certTree 8 10 + 183 * certTree 8 11 = _
  rw [certBlock10, certBlock11]
  norm_num
private theorem certLevel9_6 : certTree 9 6 = (69913351433479938009062436988768102942220742352093193566235185937504751505873407632618568488218657891704696020493110213676479464979777910529014443131505728564466824636608615568640) := by
  change 183 * certTree 8 12 + 17 * certTree 8 13 = _
  rw [certBlock12, certBlock13]
  norm_num
private theorem certLevel9_7 : certTree 9 7 = (67844702736624737762857246615120930047086014969830815532528493461617699021322063397465732726169321287703446481015841429341518916164044762217073932658487844548570158168878635002624) := by
  change 17 * certTree 8 14 + 183 * certTree 8 15 = _
  rw [certBlock14, certBlock15]
  norm_num
private theorem certLevel9_8 : certTree 9 8 = (67444749956633777064480672115724293125243950250211795418387025391500394432065330358676431722656355919089524177607425445839863487885760828237800674484275057737365497164175811040512) := by
  change 183 * certTree 8 16 + 17 * certTree 8 17 = _
  rw [certBlock16, certBlock17]
  norm_num
private theorem certLevel9_9 : certTree 9 9 = (64819291952819049450461550501342675118919985010553512268240148500329277077248416202346931358786030200668004432428693065487123278575640835939455104920396757860404948335662695164672) := by
  change 17 * certTree 8 18 + 183 * certTree 8 19 = _
  rw [certBlock18, certBlock19]
  norm_num
private theorem certLevel9_10 : certTree 9 10 = (64326609658794260494741374265961766967080622052066287039166421638014356404463425888491659809679846299557532170972913009340486501069722623566885939999794979254160764361686585464064) := by
  change 183 * certTree 8 20 + 17 * certTree 8 21 = _
  rw [certBlock20, certBlock21]
  norm_num
private theorem certLevel9_11 : certTree 9 11 = (61169626901138439628430658986274796168290369634760290521928864133205073619103876718908545269568879287802985248530962340764152273641226976187596624905890692769719970078989428960000) := by
  change 17 * certTree 8 22 + 183 * certTree 8 23 = _
  rw [certBlock22, certBlock23]
  norm_num
private theorem certLevel9_12 : certTree 9 12 = (60588959884889739458114978691188271963440276935933428189353230977845447508773888386732726458017337146675253664788992445275049375179157924780537761043171436417658736108405484180736) := by
  change 183 * certTree 8 24 + 17 * certTree 8 25 = _
  rw [certBlock24, certBlock25]
  norm_num
private theorem certLevel9_13 : certTree 9 13 = (56930855791811225330902308624566714863561539252184258499288208238602909437828616484557091289886291308807548971960936748792787826696119729039503055832665392931803864796530396867328) := by
  change 17 * certTree 8 26 + 183 * certTree 8 27 = _
  rw [certBlock26, certBlock27]
  norm_num
private theorem certLevel9_14 : certTree 9 14 = (56267796184690600560105688054437096983688510071020075067298717862495985023597755429294810087432870083880148155767037696530248329942987365315856649514593488541563673393260517676288) := by
  change 183 * certTree 8 28 + 17 * certTree 8 29 = _
  rw [certBlock28, certBlock29]
  norm_num
private theorem certLevel9_15 : certTree 9 15 = (52143800238862399688729598646465567702932564060196585557034499058028506796099830805174734035422226633247356860836865622934368676387450904765409115344840490357542342359738612165376) := by
  change 17 * certTree 8 30 + 183 * certTree 8 31 = _
  rw [certBlock30, certBlock31]
  norm_num
private theorem certLevel9_16 : certTree 9 16 = (51404733656572910864652688685802069805249528101718747730880390250259960404630589347929825682890926079505358405729840645368479395781721909294535326463882597043075439285643601532160) := by
  change 183 * certTree 8 32 + 17 * certTree 8 33 = _
  rw [certBlock32, certBlock33]
  norm_num
private theorem certLevel9_17 : certTree 9 17 = (46854562126318628582505684348793029660938642389750378365683405245369117127097234762410412877842561732274845542647182638350780111765838846468072196720625640819088149260994505845504) := by
  change 17 * certTree 8 34 + 183 * certTree 8 35 = _
  rw [certBlock34, certBlock35]
  norm_num
private theorem certLevel9_18 : certTree 9 18 = (46046606172048203925379506733619528220268302286718837924010166936862384816897445918588210033732044110518720107557824324001628776539241224208838901873080409233426687051696606565632) := by
  change 183 * certTree 8 36 + 17 * certTree 8 37 = _
  rw [certBlock36, certBlock37]
  norm_num
private theorem certLevel9_19 : certTree 9 19 = (41114079622611883984287833297852619879519727172228246361771302501532772866786333680465424357549912044828535876499876892248871112052428798469478017489104645770536788636852655991552) := by
  change 17 * certTree 8 38 + 183 * certTree 8 39 = _
  rw [certBlock38, certBlock39]
  norm_num
private theorem certLevel9_20 : certTree 9 20 = (40245015340739214512646711933951129390540131390575262225698120251105595635395259601400110616400953013268709890771444060800631756782280108121639550232517951985930703130722735510784) := by
  change 183 * certTree 8 40 + 17 * certTree 8 41 = _
  rw [certBlock40, certBlock41]
  norm_num
private theorem certLevel9_21 : certTree 9 21 = (34977636618997014623584838227593198934714798771342997287468704377409502346500297826037125623966875208778095737802046025039675983277720509967966071944621261353109553911855503092480) := by
  change 17 * certTree 8 42 + 183 * certTree 8 43 = _
  rw [certBlock42, certBlock43]
  norm_num
private theorem certLevel9_22 : certTree 9 22 = (34055833559506329009838626601253452799831191904963569132464981339034802389304649774090292530566349341739327725172656989424861674628862979623805998038598994779166420664773753984256) := by
  change 183 * certTree 8 44 + 17 * certTree 8 45 = _
  rw [certBlock44, certBlock45]
  norm_num
private theorem certLevel9_23 : certTree 9 23 = (28504330316347204328066917571619740938578360305336120766282545639749068888881938349244670920519973597444241514069334595992971627265997901878570169982642975335218826133828592446208) := by
  change 17 * certTree 8 46 + 183 * certTree 8 47 = _
  rw [certBlock46, certBlock47]
  norm_num
private theorem certLevel9_24 : certTree 9 24 = (27538665931620289979026153389566819334915543369452383100271287542028521585447576168871982089935615111656271364252306888908600770950843327020514449987526145470890666574802044081408) := by
  change 183 * certTree 8 48 + 17 * certTree 8 49 = _
  rw [certBlock48, certBlock49]
  norm_num
private theorem certLevel9_25 : certTree 9 25 = (21756502087737745580786007939622259718793807414865463672007320080269919214807899274876945885090754400425123176845544969689952639824090491521416298871394464372580430194421586701056) := by
  change 17 * certTree 8 50 + 183 * certTree 8 51 = _
  rw [certBlock50, certBlock51]
  norm_num
private theorem certLevel9_26 : certTree 9 26 = (20756276237972224811239579452546527698787303629301756323093269138430959812940771232150396634256228775238711673542120161861010510013112839101299327629530944435171788610393192551680) := by
  change 183 * certTree 8 52 + 17 * certTree 8 53 = _
  rw [certBlock52, certBlock53]
  norm_num
private theorem certLevel9_27 : certTree 9 27 = (14799137097886846739698174232876887649283682905006146937813621923444667287713842548610019124906242308164394466368070724355200080003495172038663120382737955453988552760015172643584) := by
  change 17 * certTree 8 54 + 183 * certTree 8 55 = _
  rw [certBlock54, certBlock55]
  norm_num
private theorem certLevel9_28 : certTree 9 28 = (13773982488492854368612611374011838787053736070957561031356216238077674552733357184095072355473103272245433683538024413397725531552168845462092866745165208308660057170122668266752) := by
  change 183 * certTree 8 56 + 17 * certTree 8 57 = _
  rw [certBlock56, certBlock57]
  norm_num
private theorem certLevel9_29 : certTree 9 29 = (7699238461378175275890897459419342494153699699730138432499806847474707886039223559445321612839284167771695680395761740596359894611920692194176711031557158121414002117893663730432) := by
  change 17 * certTree 8 58 + 183 * certTree 8 59 = _
  rw [certBlock58, certBlock59]
  norm_num
private theorem certLevel9_30 : certTree 9 30 = (6659027874875950699381255131053630447527488898416526975584002096211951634123932724820566731303464200295961959012253476898786473728070488437695965585586689483568498742758297064704) := by
  change 183 * certTree 8 60 + 17 * certTree 8 61 = _
  rw [certBlock60, certBlock61]
  norm_num
private theorem certLevel9_31 : certTree 9 31 = (525181966731826396299317668431589142792279878304143472292778411018936922758859402686698543545561434933879750802011786893061219384930533837176865796047085073501143651065955592960) := by
  change 17 * certTree 8 62 + 183 * certTree 8 63 = _
  rw [certBlock62, certBlock63]
  norm_num
private theorem certLevel9_32 : certTree 9 32 = (-520066817469681267216552345759926627682988691535444225831234307427670851801909263231704244830164683684281604956369691303285775100465826871492071794789639266530657238649611463424) := by
  change 183 * certTree 8 64 + 17 * certTree 8 65 = _
  rw [certBlock64, certBlock65]
  norm_num
private theorem certLevel9_33 : certTree 9 33 = (-6653942419566224295481862328999281829882584077872809047776450350407512423261332421262401979845870121590162371467162152248870221984461098859891157840458785301783925137728145478912) := by
  change 17 * certTree 8 66 + 183 * certTree 8 67 = _
  rw [certBlock66, certBlock67]
  norm_num
private theorem certLevel9_34 : certTree 9 34 = (-7694163101886533108846760340724669871683761276503165641530580101609283796777670536655107189128032306204235268727306724980012408203410455458368013893433184016284115764724518857472) := by
  change 183 * certTree 8 68 + 17 * certTree 8 69 = _
  rw [certBlock68, certBlock69]
  norm_num
private theorem certLevel9_35 : certTree 9 35 = (-13768995927860752572282749780217534025135109162716403540003322711465752278165227892190404467618912226908930990923500921573367148867466872496709453418032517858945701980700636894464) := by
  change 17 * certTree 8 70 + 183 * certTree 8 71 = _
  rw [certBlock70, certBlock71]
  norm_num
private theorem certLevel9_36 : certTree 9 36 = (-14794170632730290892123963100106801622895149116171692438141672854532232285737579433375917689269996666262132881570941551735944985706292230772009277261602565735338117349290407340800) := by
  change 183 * certTree 8 72 + 17 * certTree 8 73 = _
  rw [certBlock72, certBlock73]
  norm_num
private theorem certLevel9_37 : certTree 9 37 = (-20751456831850188369162665570312871977039896721944508522290032244187828275952071364719288331166843675868019110907906120074507472697477733394545519448369446695681829565798011131136) := by
  change 17 * certTree 8 74 + 183 * certTree 8 75 = _
  rw [certBlock74, certBlock75]
  norm_num
private theorem certLevel9_38 : certTree 9 38 = (-21751712585895906750183182557817610372454756194445075161946348943032705123610038236941902710152146715854241572128770769508320534674431469275102882821773189777364807387624348560128) := by
  change 183 * certTree 8 76 + 17 * certTree 8 77 = _
  rw [certBlock76, certBlock77]
  norm_num
private theorem certLevel9_39 : certTree 9 39 = (-27534080355795650539429921652052097894036940547473388219899141644445357680488520956621456300355440632962355094660469673850385416630664011683572502004993963152301610078875828114688) := by
  change 17 * certTree 8 78 + 183 * certTree 8 79 = _
  rw [certBlock78, certBlock79]
  norm_num
private theorem certLevel9_40 : certTree 9 40 = (-28499784171170556800810188441215670332216824644245846256440979537273359326988702433858545593185866671432142169997805754483489875827898127618717157207451568723657139005305177746176) := by
  change 183 * certTree 8 80 + 17 * certTree 8 81 = _
  rw [certBlock80, certBlock81]
  norm_num
private theorem certLevel9_41 : certTree 9 41 = (-34051546289547458688615530954021130723529670902174275918729835749367208187566831948049201082622692689604276364659269632396669832065159124137454166095706146400595217341221817570560) := by
  change 17 * certTree 8 82 + 183 * certTree 8 83 = _
  rw [certBlock82, certBlock83]
  norm_num
private theorem certLevel9_42 : certTree 9 42 = (-34973397937160975701871986969942091273325732145965177163453082139970380170514730683976117431833581775463181711679048106628877963109070315668818908003702570963052522082770696514304) := by
  change 183 * certTree 8 84 + 17 * certTree 8 85 = _
  rw [certBlock84, certBlock85]
  norm_num
private theorem certLevel9_43 : certTree 9 43 = (-40241088078429548747682631096565886862452906870527878641883641135699976235169423289301835637334782791860125703371753340329896997401494339680419071623163825263048089940273591244032) := by
  change 17 * certTree 8 86 + 183 * certTree 8 87 = _
  rw [certBlock86, certBlock87]
  norm_num
private theorem certLevel9_44 : certTree 9 44 = (-41110209658366751809711209799667624610519764543446700058550287548440569447250489038502006044463553385127209152784818239440161915021982634728170796654779408486625279026872738884352) := by
  change 183 * certTree 8 88 + 17 * certTree 8 89 = _
  rw [certBlock88, certBlock89]
  norm_num
private theorem certLevel9_45 : certTree 9 45 = (-46043097335775359823789038582632979892981208900558955776529370228554753889000442758848650296174530807954501565133070673467393413653827543842691415706699622639292481476937055229184) := by
  change 17 * certTree 8 90 + 183 * certTree 8 91 = _
  rw [certBlock90, certBlock91]
  norm_num
private theorem certLevel9_46 : certTree 9 46 = (-46851118783467998685165917205383422482699090141035973468949954734156046948057545061925088853353574078814033439129730696776120048701261065856901823520926501614193894029544498113280) := by
  change 183 * certTree 8 92 + 17 * certTree 8 93 = _
  rw [certBlock92, certBlock93]
  norm_num
private theorem certLevel9_47 : certTree 9 47 = (-51401697966125596463224079416821310941120358316878581313740787323584238324354917393665678705273251930637798383386171009570195096169027181288413389512127347682459872911818236646656) := by
  change 17 * certTree 8 94 + 183 * certTree 8 95 = _
  rw [certBlock94, certBlock95]
  norm_num
private theorem certLevel9_48 : certTree 9 48 = (-52140837672617567500338174774835724904285453984249464185336783588761834127095004733007117240202602939333652786667172827893235143599845197106677249256787113871538787999306723339008) := by
  change 183 * certTree 8 96 + 17 * certTree 8 97 = _
  rw [certBlock96, certBlock97]
  norm_num
private theorem certLevel9_49 : certTree 9 49 = (-56265284384954539662898146943801413947727614661023811046686172055434894541128603330053696462449127782221149608885763240322611028165740289114825581074219140686684248708287572759808) := by
  change 17 * certTree 8 98 + 183 * certTree 8 99 = _
  rw [certBlock98, certBlock99]
  norm_num
private theorem certLevel9_50 : certTree 9 50 = (-56928424157590055936690859297956831673172905666726732213476880369781184524516930493284305962125452809096157307295625056997859911474304870039262789578628059056932516628201449433856) := by
  change 183 * certTree 8 100 + 17 * certTree 8 101 = _
  rw [certBlock100, certBlock101]
  norm_num
private theorem certLevel9_51 : certTree 9 51 = (-60587018674073036790158919823973943010967234079509920677981955818693517091069196031495108400304949283247800019926903108634715731184868019960869643293001965115659600477300596430080) := by
  change 17 * certTree 8 102 + 183 * certTree 8 103 = _
  rw [certBlock102, certBlock103]
  norm_num
private theorem certLevel9_52 : certTree 9 52 = (-61167772319776537172657986857432941815138959318187664969554923526120199437841770759953780164767627840460210605882895524496716043130343166402144263763806371212541128132316528880384) := by
  change 183 * certTree 8 104 + 17 * certTree 8 105 = _
  rw [certBlock104, certBlock105]
  norm_num
private theorem certLevel9_53 : certTree 9 53 = (-64325281918024193223333191424894424760410089720849655700630844069764770145726058195993082285284687333395126914968071905936880670479966262804367695215490036085802442856237424465152) := by
  change 17 * certTree 8 106 + 183 * certTree 8 107 = _
  rw [certBlock106, certBlock107]
  norm_num
private theorem certLevel9_54 : certTree 9 54 = (-64818056794645424785895610843583889416451772413846504143406425934928257832620084633816666312194812360555490847964829224786005825363278215337707593970058376986151628748268665023232) := by
  change 183 * certTree 8 108 + 17 * certTree 8 109 = _
  rw [certBlock108, certBlock109]
  norm_num
private theorem certLevel9_55 : certTree 9 55 = (-67444075423056456686527408787569815171346465885734792095401840692549795270693702788432051078590410151554162909867693259827252613201568414987658366921212668575849429570978952271104) := by
  change 17 * certTree 8 110 + 183 * certTree 8 111 = _
  rw [certBlock110, certBlock111]
  norm_num
private theorem certLevel9_56 : certTree 9 56 = (-67844126374601874067177670749190920482107823015855303779498384318683302829527782020077920158304308900019653445774751781201340996289360375838227878509772428970238020179451531733760) := by
  change 183 * certTree 8 112 + 17 * certTree 8 113 = _
  rw [certBlock112, certBlock113]
  norm_num
private theorem certLevel9_57 : certTree 9 57 = (-69913368023685947369041957377237318940302257270281938232207465258140310854187460520269136524297308614569066164113157220438617668873238793417598566528132789517790331355975991710976) := by
  change 17 * certTree 8 114 + 183 * certTree 8 115 = _
  rw [certBlock114, certBlock115]
  norm_num
private theorem certLevel9_58 : certTree 9 58 = (-70216843192213866329182961924718498747176198400869878452573643167827169976887400488790864259685593629359922933146572335901647390957816152374255319646230300117517145554831918213888) := by
  change 183 * certTree 8 116 + 17 * certTree 8 117 = _
  rw [certBlock116, certBlock117]
  norm_num
private theorem certLevel9_59 : certTree 9 59 = (-71709386229450182316537409806369372779184844224247615957290808856599767173469303453602096736112574225061534065117141676752055033602436319888586213519718203072362173382392682140928) := by
  change 17 * certTree 8 118 + 183 * certTree 8 119 = _
  rw [certBlock118, certBlock119]
  norm_num
private theorem certLevel9_60 : certTree 9 60 = (-71913364319539016870787925053746655466334241027248100821433822581640154895024459971441591854587743558593902627996454446891067932704469359001410006553911452976774363971381319150336) := by
  change 183 * certTree 8 120 + 17 * certTree 8 121 = _
  rw [certBlock120, certBlock121]
  norm_num
private theorem certLevel9_61 : certTree 9 61 = (-72814844553277694178439749783567871964847643012500590009004986653105058804177759853753495351314678180876311405644313990083361846086837631613798619523742617375639564068736889017600) := by
  change 17 * certTree 8 122 + 183 * certTree 8 123 = _
  rw [certBlock122, certBlock123]
  norm_num
private theorem certLevel9_62 : certTree 9 62 = (-72917363213871113266719076922207473803772915542538651952841042920377070931124108738875510271745514151395551033492464259435322742603637974046697742389668038838372207448708807633664) := by
  change 183 * certTree 8 124 + 17 * certTree 8 125 = _
  rw [certBlock124, certBlock125]
  norm_num
private theorem certLevel9_63 : certTree 9 63 = (-73219113990217407837253318934684821044203713841865507001930643769754893625112242704303280161176222160755209062273526380776768715069665614893221283519329074273873703277962382038272) := by
  change 17 * certTree 8 126 + 183 * certTree 8 127 = _
  rw [certBlock126, certBlock127]
  norm_num
private theorem certLevel9_64 : certTree 9 64 = (-73219164258527153255766125797570557572359128810896863101085021833153037162870800103360044713124787037201791565122659076935881405198091721564253765155309968615103144157481347296000) := by
  change 183 * certTree 8 128 + 17 * certTree 8 129 = _
  rw [certBlock128, certBlock129]
  norm_num
private theorem certLevel9_65 : certTree 9 65 = (-72918001510290515917267917201620863456925895400946218225980164928421329987498051667928509826532061650395967885728883607422969030870034087895072230230337094061729843361567776199936) := by
  change 17 * certTree 8 130 + 183 * certTree 8 131 = _
  rw [certBlock130, certBlock131]
  norm_num
private theorem certLevel9_66 : certTree 9 66 = (-72815582572510812726909168372320595745602592090378658083709964397970798207819529300555921808817611219833076528674970316183083884248248748604603307246171490848974465346203864771328) := by
  change 183 * certTree 8 132 + 17 * certTree 8 133 = _
  rw [certBlock132, certBlock133]
  norm_num
private theorem certLevel9_67 : certTree 9 67 = (-71914684720547186590109576935673367861683348071306526890115092177834014699316944282011113853775104752800798258733542976241093390939854740886069735983836052802520970248091798623488) := by
  change 17 * certTree 8 134 + 183 * certTree 8 135 = _
  rw [certBlock134, certBlock135]
  norm_num
private theorem certLevel9_68 : certTree 9 68 = (-71710804912635013111349077228889876764786218512673832215645384692684042512243410216183485940221449581756450203758334011311963133392546141231721970820759609881911813500595599813376) := by
  change 183 * certTree 8 136 + 17 * certTree 8 137 = _
  rw [certBlock136, certBlock137]
  norm_num
private theorem certLevel9_69 : certTree 9 69 = (-70218832995935469026256163976069150150844353704086827896076559468939176149874923316793120651183222922086110641684671854017031257809865993918656729019353495446363207124842092975360) := by
  change 17 * certTree 8 138 + 183 * certTree 8 139 = _
  rw [certBlock138, certBlock139]
  norm_num
private theorem certLevel9_70 : certTree 9 70 = (-69915453721565606216473835495239049259228183786146206626620959749316956179854502715848208086586310457157828883304674959264023261649798166292943916954526136574430487915862715509504) := by
  change 183 * certTree 8 140 + 17 * certTree 8 141 = _
  rw [certBlock140, certBlock141]
  norm_num
private theorem certLevel9_71 : certTree 9 71 = (-67846766427386500401123007750762395939246839094883779121528358261289829029056191279546425880279872316269691316953075892663521668879866346898726332993996335432697163836939550872832) := by
  change 17 * certTree 8 142 + 183 * certTree 8 143 = _
  rw [certBlock142, certBlock143]
  norm_num
private theorem certLevel9_72 : certTree 9 72 = (-67446808057887710051653092617008654036754781398608066152586922137552480237061357274311759212909597089151201138748297265757812497483390022301340060950990976540796997621186271095552) := by
  change 183 * certTree 8 144 + 17 * certTree 8 145 = _
  rw [certBlock144, certBlock145]
  norm_num
private theorem certLevel9_73 : certTree 9 73 = (-64821321677237906717668577189897057890589608059959054915828069698661250595154822090477204702556952619877714558629286838688440347117147926384553899193966854933415375289563203785984) := by
  change 17 * certTree 8 146 + 183 * certTree 8 147 = _
  rw [certBlock146, certBlock147]
  norm_num
private theorem certLevel9_74 : certTree 9 74 = (-64328635178555727144560148692533824609185747588987899288579347925875544859554447890214944323083135893788778565288799480603676495604148024058522228632298206135581838210977027828480) := by
  change 183 * certTree 8 148 + 17 * certTree 8 149 = _
  rw [certBlock148, certBlock149]
  norm_num
private theorem certLevel9_75 : certTree 9 75 = (-61171630593283668564637985565640494703236110550937065197851883099186109683596182626123410014315999589733250313695916454560713459262776820083437600609178646086330885723780870067456) := by
  change 17 * certTree 8 150 + 183 * certTree 8 151 = _
  rw [certBlock150, certBlock151]
  norm_num
private theorem certLevel9_76 : certTree 9 76 = (-60590960270038022529398497710065059639309512349610072713277316496305136401465808887021122747763613279536141716751278401517446542240319002639627235055677154583102965407719547710208) := by
  change 183 * certTree 8 152 + 17 * certTree 8 153 = _
  rw [certBlock152, certBlock153]
  norm_num
private theorem certLevel9_77 : certTree 9 77 = (-56932838667037503906462305536290627059702892160077477991506647119019014596965030909874685164774762220981312777607043303168989809802777708101667385627096888235933260961411823588608) := by
  change 17 * certTree 8 154 + 183 * certTree 8 155 = _
  rw [certBlock154, certBlock155]
  norm_num
private theorem certLevel9_78 : certTree 9 78 = (-56269776358781781052338744544985008332220012731728860729545863819831331915754576583989924736408688856074555615196342289250583252861374200011783376494277438204808231055942408973056) := by
  change 183 * certTree 8 156 + 17 * certTree 8 157 = _
  rw [certBlock156, certBlock157]
  norm_num
private theorem certLevel9_79 : certTree 9 79 = (-52145765905291064301550257259674285070335812042575517169083029270596832769039098391757335520091200797489452867068985288889003177591350663265712349087451249320292311611129916314880) := by
  change 17 * certTree 8 158 + 183 * certTree 8 159 = _
  rw [certBlock158, certBlock159]
  norm_num
private theorem certLevel9_80 : certTree 9 80 = (-51406697058979284080768383490083401941635845962291670637804737646519077193457103218249562335704079365759144996840631662947039323371995486303859454077661885269917534826115478563584) := by
  change 183 * certTree 8 160 + 17 * certTree 8 161 = _
  rw [certBlock160, certBlock161]
  norm_num
private theorem certLevel9_81 : certTree 9 81 = (-46856513278671705445588603565963377885918815422032367152177242748223980236210519823362923098074884406714055526343900346861900759510556915994924617934641489405416619082330778653952) := by
  change 17 * certTree 8 162 + 183 * certTree 8 163 = _
  rw [certBlock162, certBlock163]
  norm_num
private theorem certLevel9_82 : certTree 9 82 = (-46048555404478082850337706805611804590150345333310784219774183857305492970766622014754842594007059812615574995254721476988017955184031033248092522999434702818617548684928068594432) := by
  change 183 * certTree 8 164 + 17 * certTree 8 165 = _
  rw [certBlock164, certBlock165]
  norm_num
private theorem certLevel9_83 : certTree 9 83 = (-41116018464711745569732284896871349381844081165543605055968770580554171857423224290238500129823526470508900840162788271829763844353896491643732651702190219172988199432518009115904) := by
  change 17 * certTree 8 166 + 183 * certTree 8 167 = _
  rw [certBlock166, certBlock167]
  norm_num
private theorem certLevel9_84 : certTree 9 84 = (-40246952559309515840492950795084477733424450440081994805482356239730248335978124962871242691488496556512476389479446983873486757547483441149806967463539915857300280610400011528960) := by
  change 183 * certTree 8 168 + 17 * certTree 8 169 = _
  rw [certBlock168, certBlock169]
  norm_num
private theorem certLevel9_85 : certTree 9 85 = (-34979565113021033571919574378780220567034581763547449782223850638460600893204477222947683907991640328979604751082852632968955318608857186920554836869386425195488053200521924203776) := by
  change 17 * certTree 8 170 + 183 * certTree 8 171 = _
  rw [certBlock170, certBlock171]
  norm_num
private theorem certLevel9_86 : certTree 9 86 = (-34057760704781768438625062844241149003897355044282434739803305758332485609213871847648275486359974770146445741420432459941222710016260308866568756600313345408093720037065291705088) := by
  change 183 * certTree 8 172 + 17 * certTree 8 173 = _
  rw [certBlock172, certBlock173]
  norm_num
private theorem certLevel9_87 : certTree 9 87 = (-28506250323513719440258208800864306897163683620002680382311826837249003924809070253395776486330476951423658893665058378635052703191025530819174608824690950814853397815272596329728) := by
  change 17 * certTree 8 174 + 183 * certTree 8 175 = _
  rw [certBlock174, certBlock175]
  norm_num
private theorem certLevel9_88 : certTree 9 88 = (-27540584857399847290786609278841058031350126909023651446873495311416655624944562593739553333905693312563852683061776545258773350236783467022748599890134611291877094303853873441536) := by
  change 183 * certTree 8 176 + 17 * certTree 8 177 = _
  rw [certBlock176, certBlock177]
  norm_num
private theorem certLevel9_89 : certTree 9 89 = (-21758415442321531803554829788109060482212093674252438876069237763172293869823458661925137787253342149411787838067667065591146828098111711590705703159722668457019470697428893062400) := by
  change 17 * certTree 8 178 + 183 * certTree 8 179 = _
  rw [certBlock178, certBlock179]
  norm_num
private theorem certLevel9_90 : certTree 9 90 = (-20758188778093053043516312798513881178680900990509094753059569096467025039451951295060051591854689825711518940263099859735307611653987115013748802441635631274346999594111348484864) := by
  change 183 * certTree 8 180 + 17 * certTree 8 181 = _
  rw [certBlock180, certBlock181]
  norm_num
private theorem certLevel9_91 : certTree 9 91 = (-14801045641215103389003797020602243178435735017164642568040223696095916183803856136806691133707579761099166672423496070726711457362869445463692442762605484709182491221950699427072) := by
  change 17 * certTree 8 182 + 183 * certTree 8 183 = _
  rw [certBlock182, certBlock183]
  norm_num
private theorem certLevel9_92 : certTree 9 92 = (-13775890486564924231641941916951107191450684643559385852707102160019177547014433732242464875842271939868416620303082872500124479424720117542135407250714940463702287239722025069312) := by
  change 183 * certTree 8 184 + 17 * certTree 8 185 = _
  rw [certBlock184, certBlock185]
  norm_num
private theorem certLevel9_93 : certTree 9 93 = (-7701144052471922180481859104784650662216253589793900481350757422641274884636130172361948529824998137029438208842620852453796443296467819354645878881896368831899619171570314401024) := by
  change 17 * certTree 8 186 + 183 * certTree 8 187 = _
  rw [certBlock186, certBlock187]
  norm_num
private theorem certLevel9_94 : certTree 9 94 = (-6660933192492159074960507979381856688352368584818991760858663691852248787183841473200292906244238790715299864344594230221778883509752298307242920199544198756868725704489710365440) := by
  change 183 * certTree 8 188 + 17 * certTree 8 189 = _
  rw [certBlock188, certBlock189]
  norm_num
private theorem certLevel9_95 : certTree 9 95 = (-527086479908217543105545207146625590186960374126298551456402921839701884353528444586229088179152268436818508643514319412875604634645030595663025357907882424059082891147868656896) := by
  change 17 * certTree 8 190 + 183 * certTree 8 191 = _
  rw [certBlock190, certBlock191]
  norm_num
private theorem certLevel9_96 : certTree 9 96 = (518162304426894838755710766338007942376770087998434764805060011099146254326159462385432915374996691350911429043876071741950768662430948613593412883397896368867136372610757580032) := by
  change 183 * certTree 8 192 + 17 * certTree 8 193 = _
  rw [certBlock192, certBlock193]
  norm_num
private theorem certLevel9_97 : certTree 9 97 = (6652037103652459498541750686884261595695911454930883354072866747646912912636517505682465186838250007170214919003412627302931999682220014976073586963874913998575572495063527697152) := by
  change 17 * certTree 8 194 + 183 * certTree 8 195 = _
  rw [certBlock194, certBlock195]
  norm_num
private theorem certLevel9_98 : certTree 9 98 = (7692257512761632677721707899885209150687598023559362484791147092739556849195723924623201024454790017780275717113741232291889492730763663517124549894317088389017062832936123389184) := by
  change 183 * certTree 8 196 + 17 * certTree 8 197 = _
  rw [certBlock196, certBlock197]
  norm_num
private theorem certLevel9_99 : certTree 9 99 = (13767087933317305326205351880533424780604557535694301247830104374982868431148565883664316302138705459136740544604477753873725812424357176199637268204090401144602548025738948750080) := by
  change 17 * certTree 8 198 + 183 * certTree 8 199 = _
  rw [certBlock198, certBlock199]
  norm_num
private theorem certLevel9_100 : certTree 9 100 = (14792262093194898328716798243713465039176132767553649960749437132479033690570743514703435628347027768808285001834246834423431216572669159571106734457553056739164257288985649894656) := by
  change 183 * certTree 8 200 + 17 * certTree 8 201 = _
  rw [certBlock200, certBlock201]
  norm_num
private theorem certLevel9_101 : certTree 9 101 = (20749544297067047138974820379901183820177624400743116049735179524058868854071046811014089027424346336880415017940501923419606777052685689513830628894232883320725464564950793431808) := by
  change 17 * certTree 8 202 + 183 * certTree 8 203 = _
  rw [certBlock202, certBlock203]
  norm_num
private theorem certLevel9_102 : certTree 9 102 = (21749799236911392235864098088109542093595504093792283618162482662958766706415441577630789349461524520230718274382778438410111583769623613849838477633673647201804425226392316695808) := by
  change 183 * certTree 8 204 + 17 * certTree 8 205 = _
  rw [certBlock204, certBlock205]
  norm_num
private theorem certLevel9_103 : certTree 9 103 = (27532161437146716170715362161564631417405794366052264979506646426991886957483648411087773108079771382275921019217668042076278179810645523686712156169293894739010126945103279270656) := by
  change 17 * certTree 8 206 + 183 * certTree 8 207 = _
  rw [certBlock206, certBlock207]
  norm_num
private theorem certLevel9_104 : certTree 9 104 = (28497864171394830951786777564664211477793926489630767813535620381239171615894591305765966947332970128351300892276813866727608785247735949771038159079755094142562265349968895694080) := by
  change 183 * certTree 8 208 + 17 * certTree 8 209 = _
  rw [certBlock208, certBlock209]
  norm_num
private theorem certLevel9_105 : certTree 9 105 = (34049619153196011293880266519775987237915819207253017539142179254130462773381531144934273597189200839038089161599893974655935241983377118394532512936211127553624439430943165885184) := by
  change 17 * certTree 8 210 + 183 * certTree 8 211 = _
  rw [certBlock210, certBlock211]
  norm_num
private theorem certLevel9_106 : certTree 9 106 = (34971469452324059569267218666145394126068755321340177074117201280487237286582422828879651978945051521085889760197016664941486697669593111991820080073689408659487552079385255761152) := by
  change 183 * certTree 8 212 + 17 * certTree 8 213 = _
  rw [certBlock212, certBlock213]
  norm_num
private theorem certLevel9_107 : certTree 9 107 = (40239150870621003340567209011571579451373266058817019399423745856254394905862142000364491311831984332695896010718491405428891545749269272515581637234715720199794632491952850316032) := by
  change 17 * certTree 8 214 + 183 * certTree 8 215 = _
  rw [certBlock214, certBlock215]
  norm_num
private theorem certLevel9_108 : certTree 9 108 = (41108270827304439699967219604098382251276977481468538876815428770456907762180982351680199035119992816285017002772263872337368483511448497750755517904966721610261552099526161487104) := by
  change 183 * certTree 8 216 + 17 * certTree 8 217 = _
  rw [certBlock216, certBlock217]
  norm_num
private theorem certLevel9_109 : certTree 9 109 = (46041148116079839078219533031510741881756395129349766225372531355542805972750626821337008432793145553912845002955749288418162351231196879553998189051439979390738485129502269090560) := by
  change 17 * certTree 8 218 + 183 * certTree 8 219 = _
  rw [certBlock218, certBlock219]
  norm_num
private theorem certLevel9_110 : certTree 9 110 = (46849167644156479122992304641089002616309156510052565483957594589509303893013946628634619638459914379142412979898862588915022140091454000144702168622855389397975509255514964382976) := by
  change 183 * certTree 8 220 + 17 * certTree 8 221 = _
  rw [certBlock220, certBlock221]
  norm_num
private theorem certLevel9_111 : certTree 9 111 = (51399734578728315167416819243156104292059787930035766105608402514055038583800191853435722769269247342276589150696291674814152521771680492177803940336053558697068632412535165266688) := by
  change 17 * certTree 8 222 + 183 * certTree 8 223 = _
  rw [certBlock222, certBlock223]
  norm_num
private theorem certLevel9_112 : certTree 9 112 = (52138872021569995047436879873363206593734023116046446508480233286454296538267483683825283842237264496906944917079777497843016455355815004925464016395842374409337606256883668636928) := by
  change 183 * certTree 8 224 + 17 * certTree 8 225 = _
  rw [certBlock224, certBlock225]
  norm_num
private theorem certLevel9_113 : certTree 9 113 = (56263304228740925367231029076173134296831100669904154818722686877088725128500524907068402921770635975475398352014608051431946381176351186346909087516941703226066096023877067451136) := by
  change 17 * certTree 8 226 + 183 * certTree 8 227 = _
  rw [certBlock226, certBlock227]
  norm_num
private theorem certLevel9_114 : certTree 9 114 = (56926441300735014995679581476820968954902102801422751303187227653647493359802053594047577363701891004734691964946942461247223395004144286195469158536079809649738338129928810681600) := by
  change 183 * certTree 8 228 + 17 * certTree 8 229 = _
  rw [certBlock228, certBlock229]
  norm_num
private theorem certLevel9_115 : certTree 9 115 = (60585018310753311354030018983977978169432899753638353933381762391636838702762909527208473235151051726244710796457169652313425307887485152711304682598045331900084687661118376094464) := by
  change 17 * certTree 8 230 + 183 * certTree 8 231 = _
  rw [certBlock230, certBlock231]
  norm_num
private theorem certLevel9_116 : certTree 9 116 = (61165768650168931413775649992748757271501571218516381757948510163298768329732923323518017710787013398404999046585642724299756001952167531748415589338998397188672801873056811734272) := by
  change 183 * certTree 8 232 + 17 * certTree 8 233 = _
  rw [certBlock232, certBlock233]
  norm_num
private theorem certLevel9_117 : certTree 9 117 = (64323256425920622343914579796039252886917036016870232095414761258730288304031548077589988631332914687497856892304294033803224283033678094759533667685073791590554543224351578630912) := by
  change 17 * certTree 8 234 + 183 * certTree 8 235 = _
  rw [certBlock234, certBlock235]
  norm_num
private theorem certLevel9_118 : certTree 9 118 = (64816027098959494218553575317577815275123779913454375824731023288234132123225441491044628189001709914854685674447710036835329157986488463722894668499858125588918357986118836180224) := by
  change 183 * certTree 8 236 + 17 * certTree 8 237 = _
  rw [certBlock236, certBlock237]
  norm_num
private theorem certLevel9_119 : certTree 9 119 = (67442017358434055149986782705490646838236405505893078737607966044981520000420191853353420188945117316327081219691897313943450087491374847547300358780877411992747941887980063927040) := by
  change 17 * certTree 8 238 + 183 * certTree 8 239 = _
  rw [certBlock238, certBlock239]
  norm_num
private theorem certLevel9_120 : certTree 9 120 = (67842062722149479991132299943990937559148046832311782040617342870362104853068860248869691380291238047920863320751138741777201532025218234636615166206624386788447068289346907428096) := by
  change 183 * certTree 8 240 + 17 * certTree 8 241 = _
  rw [certBlock240, certBlock241]
  norm_num
private theorem certLevel9_121 : certTree 9 121 = (69911265786324164461447724907326727219583576055139670252456448227970179411818716056370725579928520892628880917420442071009285351002524267370338049694826411478297246616530888141568) := by
  change 17 * certTree 8 242 + 183 * certTree 8 243 = _
  rw [certBlock242, certBlock243]
  norm_num
private theorem certLevel9_122 : certTree 9 122 = (70214733191679688705225657452786017949184194458810866261541095803409934512078530447960468414096722672057761092066094143291569284212323631786485713099686444629944285531162149410048) := by
  change 183 * certTree 8 244 + 17 * certTree 8 245 = _
  rw [certBlock244, certBlock245]
  norm_num
private theorem certLevel9_123 : certTree 9 123 = (71707221537542155872247870009331223095383711549008377762346595104748710883709115805614460145087457439934042146485626173635484845999435385865739305662914999812745819607609810332416) := by
  change 17 * certTree 8 246 + 183 * certTree 8 247 = _
  rw [certBlock246, certBlock247]
  norm_num
private theorem certLevel9_124 : certTree 9 124 = (71911188432465235777799765578220802113069898939458852028763974226137349882452200272204841171081370280630242521118887052561183219225311493970466826314144591771459331877227774629120) := by
  change 183 * certTree 8 248 + 17 * certTree 8 249 = _
  rw [certBlock248, certBlock249]
  norm_num
private theorem certLevel9_125 : certTree 9 125 = (72812588605629708617371862507312284277896970690441929482523797249949051993471442880662870649240273017405647791279162775758904915083643912316050926419567105328598456820418574002944) := by
  change 17 * certTree 8 250 + 183 * certTree 8 251 = _
  rw [certBlock250, certBlock251]
  norm_num
private theorem certLevel9_126 : certTree 9 126 = (72915090680738289136138991185575269118432351171563777634256912439893698409553036694657331237004674528226209549072919490316784697606926863965226128181888769897019603946158339675392) := by
  change 183 * certTree 8 252 + 17 * certTree 8 253 = _
  rw [certBlock252, certBlock253]
  norm_num
private theorem certLevel9_127 : certTree 9 127 = (73216721719434962995312203942150053532166349621876306701878267939383181188061046787013985989499450855333010919485521967807517343463534046754108726312929223341382119220163473025792) := by
  change 17 * certTree 8 254 + 183 * certTree 8 255 = _
  rw [certBlock254, certBlock255]
  norm_num
private theorem certLevel10_0 : certTree 10 0 = (14638236634710540634159677127470317528115505857752354872740889119731530792144001005105862237233326638476714798734575355097742632601734097065703971874102105464628808270275131563515392) := by
  change 183 * certTree 9 0 + 17 * certTree 9 1 = _
  rw [certLevel9_0, certLevel9_1]
  norm_num
private theorem certLevel10_1 : certTree 10 1 = (14397815653198648744562918158537451989744607239039241878509840053958562914652081666315758617965377219303999167505621940642327708409400888319614194184158014186629810886861963355808256) := by
  change 17 * certTree 9 2 + 183 * certTree 9 3 = _
  rw [certLevel9_2, certLevel9_3]
  norm_num
private theorem certLevel10_2 : certTree 10 2 = (14316365437055639803092122970233735879456805410110740262918236858637570562246837055430070286732356677401939190271373505628237960822475201592502201227522109494026514873154476252274176) := by
  change 183 * certTree 9 4 + 17 * certTree 9 5 = _
  rw [certLevel9_4, certLevel9_5]
  norm_num
private theorem certLevel10_3 : certTree 10 3 = (13604107575171485956756937559376187948634493359464623533078712464413619696501785531490744753188702979808710538374281855201998112562676415964717775209738872937984274963727136670147072) := by
  change 17 * certTree 9 6 + 183 * certTree 9 7 = _
  rw [certLevel9_6, certLevel9_7]
  norm_num
private theorem certLevel10_4 : certTree 10 4 = (13444317205261905043457809355700371118941282640968168270124908171150169891381178531077684838345475646604738999853446638701976114018880125778488260214269080449564770102750439238213120) := by
  change 183 * certTree 9 8 + 17 * certTree 9 9 = _
  rw [certLevel9_8, certLevel9_9]
  norm_num
private theorem certLevel10_5 : certTree 10 5 = (12287594087107836880413413957009637737237508218046260045178811304222772531171887679664622001095662296760424347387705629518628136594529821242967243337774511424179487518603737452569088) := by
  change 17 * certTree 9 10 + 183 * certTree 9 11 = _
  rw [certLevel9_10, certLevel9_11]
  norm_num
private theorem certLevel10_6 : certTree 10 6 = (12055604207395613151460380347105087921990116846562949753139540809001966354548708055009559493745239650091299753179721542214811428711619935628509962220055684544272214409379220351819264) := by
  change 183 * certTree 9 12 + 17 * certTree 9 13 = _
  rw [certLevel9_12, certLevel9_13]
  norm_num
private theorem certLevel10_7 : certTree 10 7 = (10498867978851559352559313249228629538359363894223316433081391531281648489087430879644988099968626265310228824181186049838003689387934300782439431149853899040636831099517594826760704) := by
  change 17 * certTree 9 14 + 183 * certTree 9 15 = _
  rw [certLevel9_14, certLevel9_15]
  norm_num
private theorem certLevel10_8 : certTree 10 8 = (10203593815300259374134038663431260278596620563240287266967729304968847745208050841632135118892363021998152962473562942954394991328074369790857192087141151152807303926709685679758848) := by
  change 183 * certTree 9 16 + 17 * certTree 9 17 = _
  rw [certLevel9_16, certLevel9_17]
  norm_num
private theorem certLevel10_9 : certTree 10 9 = (8306668875862794235856125107978561417696671211391989328912321195707157976509155644141172228005078654082440307227960484789571102706761570931464738532348517132976486000422878358069760) := by
  change 17 * certTree 9 18 + 183 * certTree 9 19 = _
  rw [certLevel9_18, certLevel9_19]
  norm_num
private theorem certLevel10_10 : certTree 10 10 = (7959457629878225504415290533782141060358995623588103941189723980368285541167837570098851378408811279977401537553809045552190103206878508455715460915609346656428181089423804151045632) := by
  change 183 * certTree 9 20 + 17 * certTree 9 21 = _
  rw [certLevel9_20, certLevel9_21]
  norm_num
private theorem certLevel10_11 : certTree 10 11 = (5795241618403145985203502567827721289356970198260890775481610534837671247283573764071309751474783107141864768402623399886936456258368286697383043073479847397590874333791786235388416) := by
  change 17 * certTree 9 22 + 183 * certTree 9 23 = _
  rw [certLevel9_22, certLevel9_23]
  norm_num
private theorem certLevel10_12 : certTree 10 12 = (5409436400978054741035148205264306353509039162662498989773770061555808076788640726576480802504760390240324753664546425155003135961013867200618221428530990515506859296493941040815616) := by
  change 183 * certTree 9 24 + 17 * certTree 9 25 = _
  rw [certLevel9_24, certLevel9_25]
  norm_num
private theorem certLevel10_13 : certTree 10 13 = (3061098784958820775155838735309761410698298133314254747112478387343700430471626297342190242640198231573142285795572985308638793310862534747797439599743071903477825561459460867154432) := by
  change 17 * certTree 9 26 + 183 * certTree 9 27 = _
  rw [certLevel9_26, certLevel9_27]
  norm_num
private theorem certLevel10_14 : certTree 10 14 = (2651525849237621329146253138254295320431446595880646022090684287975284477212871165199968708469845729673033190654186417241921890482449550486863998701901704808548828498136640576232960) := by
  change 183 * certTree 9 28 + 17 * certTree 9 29 = _
  rw [certLevel9_28, certLevel9_29]
  norm_num
private theorem certLevel10_15 : certTree 10 15 = (209311773784815392412256470550892530738954529002739214014506484852068634644978127013615467900996633997931347699976466108709573200819485995644197855631590289671373766771960923611648) := by
  change 17 * certTree 9 30 + 183 * certTree 9 31 = _
  rw [certLevel9_30, certLevel9_31]
  norm_num
private theorem certLevel10_16 : certTree 10 16 = (-208289248729577484923820738867054363973990859874824047139315534216191477075192046332862710461299929181256294021957410096732090617121084998101198821734303335905437002014257370948096) := by
  change 183 * certTree 9 32 + 17 * certTree 9 33 = _
  rw [certLevel9_32, certLevel9_33]
  norm_num
private theorem certLevel10_17 : certTree 10 17 = (-2650527027530588783578138135572128114418348918477655663726627917925590491449457103393980839789437486729806370907364882972586399182204415409690086211688314896463893430468533372263936) := by
  change 17 * certTree 9 34 + 183 * certTree 9 35 = _
  rw [certLevel9_34, certLevel9_35]
  norm_num
private theorem certLevel10_18 : certTree 10 18 = (-3060107991931096435534450562014863520599490532532476361058856680530591588981162249508020838766245732415726642212916708008944559420108599698984971569495550123393466577538710732595712) := by
  change 183 * certTree 9 36 + 17 * certTree 9 37 = _
  rw [certLevel9_36, certLevel9_37]
  norm_num
private theorem certLevel10_19 : certTree 10 19 = (-5408515819070834463468789765808433290940490975493196321994630852965056442630769985089738849037632130001633089049055053396261980332876849115770516874884039483086396370023890470510080) := by
  change 17 * certTree 9 38 + 183 * certTree 9 39 = _
  rw [certLevel9_38, certLevel9_39]
  norm_num
private theorem certLevel10_20 : certTree 10 20 = (-5794336790246518692254728510960826893095683315233952555547106463060267296027568688512950261957599376595354715308806036821222034421613062464561960592590641565239375132771618426249728) := by
  change 183 * certTree 9 40 + 17 * certTree 9 41 = _
  rw [certLevel9_40, certLevel9_41]
  norm_num
private theorem certLevel10_21 : certTree 10 21 = (-7958666883284344007757745269160572847475419403788009803243408724212592113934754883569829917973436141093277092815574679093062075897327659527886611543101923729509693334477169038401024) := by
  change 17 * certTree 9 42 + 183 * certTree 9 43 = _
  rw [certLevel9_42, certLevel9_43]
  norm_num
private theorem certLevel10_22 : certTree 10 22 = (-8305901022189296698181565049243935961905797462760248358915701915250055024959847020946294161171797293213505801566883939266495318481137890400581009854838525337920398247025641154732544) := by
  change 183 * certTree 9 44 + 17 * certTree 9 45 = _
  rw [certLevel9_44, certLevel9_45]
  norm_num
private theorem certLevel10_23 : certTree 10 23 = (-10202979747119940130417827125769818084430910104386391929386713310696568411473928149093545713572015862646555672624874716596539743426853412295346981280575055153331452941364993774263808) := by
  change 17 * certTree 9 46 + 183 * certTree 9 47 = _
  rw [certLevel9_46, certLevel9_47]
  norm_num
private theorem certLevel10_24 : certTree 10 24 = (-10498283128633242026831154481839561694595607528355056733710296321685808852457572122751215294818711510195818003311150602589946418757589255985473971492253767230165230431914019107955200) := by
  change 183 * certTree 9 48 + 17 * certTree 9 49 = _
  rw [certLevel9_48, certLevel9_49]
  norm_num
private theorem certLevel10_25 : certTree 10 25 = (-12055207628034396683522826935852497709450943232884669931699804881107193764582450692149438038611938416588982077870648894849116597301894030443506612145456036620133559670025433787080192) := by
  change 17 * certTree 9 50 + 183 * certTree 9 51 = _
  rw [certLevel9_50, certLevel9_51]
  norm_num
private theorem certLevel10_26 : certTree 10 26 = (-12287232127125517587393075849133433573097401080482786836339275354465997589602387038403424169002315579471935698431027103383826007291012225919266651087439896545353667976769961001017856) := by
  change 183 * certTree 9 52 + 17 * certTree 9 53 = _
  rw [certLevel9_52, certLevel9_53]
  norm_num
private theorem certLevel10_27 : certTree 10 27 = (-13444172767928303794994741192466202296436083388124857523896446087630392917691489049057948674689356867863855156921189963369749327247062749603482510244072910758145023300209715571006976) := by
  change 17 * certTree 9 54 + 183 * certTree 9 55 = _
  rw [certLevel9_54, certLevel9_55]
  norm_num
private theorem certLevel10_28 : certTree 10 28 = (-13604002382954804059567227022514972870210869985496313541595731239707429702324770938518834709882742775151270705366703248707301902691798008266494877398266611923355993325891222166364672) := by
  change 183 * certTree 9 56 + 17 * certTree 9 57 = _
  rw [certLevel9_56, certLevel9_57]
  norm_num
private theorem certLevel10_29 : certTree 10 29 = (-14316504014257019091522456347285809697292821865852101653877969954610819282351968340318628395123256174885379423779928656555954076795528721129973617508094346264240069203410003441425920) := by
  change 17 * certTree 9 58 + 183 * certTree 9 59 = _
  rw [certLevel9_58, certLevel9_59]
  norm_num
private theorem certLevel10_30 : certTree 10 30 = (-14397998027881360888387666031156291773741576039198912480475474305542934345460498092287620730361906600297581474819304501612482583068394132434692607731269420390135581195931308517810688) := by
  change 183 * certTree 9 60 + 17 * certTree 9 61 = _
  rw [certLevel9_60, certLevel9_61]
  norm_num
private theorem certLevel10_31 : certTree 10 31 = (-14638693034845594559751581672724849305753419197284544864551605539511555739224650263448383944114922395991927625965427220092549161482010653084253356504661577252371215226495165642776064) := by
  change 17 * certTree 9 62 + 183 * certTree 9 63 = _
  rw [certLevel9_62, certLevel9_63]
  norm_num
private theorem certLevel10_32 : certTree 10 32 = (-14638713084985407816398755613382966714509460794210211657340221799250168410592823297269672849552881075864659310474837632405456770676041364540474666937337454855613282717965738750566912) := by
  change 183 * certTree 9 64 + 17 * certTree 9 65 = _
  rw [certLevel9_64, certLevel9_65]
  norm_num
private theorem certLevel10_33 : certTree 10 33 = (-14398252207592818962347508441557676446363296762585531608314131263309128259507932801717484505990743560499708382335712860027232516574213646308429017908226913007293903466286264849210880) := by
  change 17 * certTree 9 66 + 183 * certTree 9 67 = _
  rw [certLevel9_66, certLevel9_67]
  norm_num
private theorem certLevel10_34 : certTree 10 34 = (-14316797459943110372823235920480023000520232000788787369696406909733145774288417765947060978130640063136894268196414545588378784793603665742022285053528018030978036391731310346428928) := by
  change 183 * certTree 9 68 + 17 * certTree 9 69 = _
  rw [certLevel9_68, certLevel9_69]
  norm_num
private theorem certLevel10_35 : certTree 10 35 = (-13604520969478344879085565621808582294289050678728217091892245877554426967374809550326415473563183911649036602018592362664912860853062110309446965526128273705948899276729603973389824) := by
  change 17 * certTree 9 70 + 183 * certTree 9 71 = _
  rw [certLevel9_70, certLevel9_71]
  norm_num
private theorem certLevel10_36 : certTree 10 36 = (-13444728343106495353652881761140833672866148332964580039492483936049345143499860356737164415905924461852590955887636275891383172940451888829682647440328785240833911944599662074847744) := by
  change 183 * certTree 9 72 + 17 * certTree 9 73 = _
  rw [certLevel9_72, certLevel9_73]
  norm_num
private theorem certLevel10_37 : certTree 10 37 = (-12287995196606358708786273886285285549048365939834277219112743521890942334710527034714238086112241235115594043016262302354873063470358674484263958798228761738103443337038508695428608) := by
  change 17 * certTree 9 74 + 183 * certTree 9 75 = _
  rw [certLevel9_74, certLevel9_75]
  norm_num
private theorem certLevel10_38 : certTree 10 38 = (-12056003986756595689289784275058846574008589926699960432385361919847163209616648551792735110641912187911796251384803683631565543996625598520780129570849566388718708105956678231974400) := by
  change 183 * certTree 9 76 + 17 * certTree 9 77 = _
  rw [certLevel9_76, certLevel9_77]
  norm_num
private theorem certLevel10_39 : certTree 10 39 = (-10499261358767555045073455735785139309519193820230710274344474041456353039301982807619421120695637456493837320131962126783947496797860532777825677283406295075095232952787795638164992) := by
  change 17 * certTree 9 78 + 183 * certTree 9 79 = _
  rw [certLevel9_78, certLevel9_79]
  norm_num
private theorem certLevel10_40 : certTree 10 40 = (-10203986287530627979355620439306639979379979673273925968305280116032798790418228725936839600101119558848062478369681900215960509088754641565519998601101030324286991397578755814253056) := by
  change 183 * certTree 9 80 + 17 * certTree 9 81 = _
  rw [certLevel9_80, certLevel9_81]
  norm_num
private theorem certLevel10_41 : certTree 10 41 = (-8307056820918376847716749151822857614910022723960763056978446141815606830411482619364477847855825360917593628669120518853643088754891585536020648152491200056573338823794572834315776) := by
  change 17 * certTree 9 82 + 183 * certTree 9 83 = _
  rw [certLevel9_82, certLevel9_83]
  norm_num
private theorem certLevel10_42 : certTree 10 42 = (-7959844925274998969532842759939723174856262320515311695701076652724465660668472980995548038978252755434436460043147292809320317047540041908064107272607373830209248256112074821263872) := by
  change 183 * certTree 9 84 + 17 * certTree 9 85 = _
  rw [certLevel9_84, certLevel9_85]
  norm_num
private theorem certLevel10_43 : certTree 10 43 = (-5795625741184300721023878278910267695247209138213291900539720509108219973596695677781447780266596853203019155144853035109215430754234097390640622277123770871055765040824995087326720) := by
  change 17 * certTree 9 86 + 183 * certTree 9 87 = _
  rw [certLevel9_86, certLevel9_87]
  norm_num
private theorem certLevel10_44 : certTree 10 44 = (-5409820091423638094874381604425767647934678816813619675671026683963176975151853751907065602488048692739185434247455447897405019170999273562204990733609919230182839259461550021861888) := by
  change 183 * certTree 9 88 + 17 * certTree 9 89 = _
  rw [certLevel9_88, certLevel9_89]
  norm_num
private theorem certLevel10_45 : certTree 10 45 = (-3061480561569945821927472172344946481691314824979784200753373611025492087306788845051645354530016823318243323037972478558488426095522889475089446667064609433444294886716870919396864) := by
  change 17 * certTree 9 90 + 183 * certTree 9 91 = _
  rw [certLevel9_90, certLevel9_91]
  norm_num
private theorem certLevel10_46 : certTree 10 46 = (-2651907407933403811458666975583391677293151600797863919228362571468411164142455585930524197286160733325420691065788720159237319270763734439239759467873072374999812090785825932501504) := by
  change 183 * certTree 9 92 + 17 * certTree 9 93 = _
  rw [certLevel9_92, certLevel9_93]
  norm_num
private theorem certLevel10_47 : certTree 10 47 = (-209692690095570514662643408557324046706204014407035494851119017458153674218821010403684902542936924566097884775621222366326476667805829670229463283889393862469580506056385040424448) := by
  change 17 * certTree 9 94 + 183 * certTree 9 95 = _
  rw [certLevel9_94, certLevel9_95]
  norm_num
private theorem certLevel10_48 : certTree 10 48 = (207908332472213566967504831916887900581779420837538578978564716741141284056507979213136131689874644639110445138087335792926834659822603850880845536047688573478470688603848607997440) := by
  change 183 * certTree 9 96 + 17 * certTree 9 97 = _
  rw [certLevel9_96, certLevel9_97]
  norm_num
private theorem certLevel10_49 : certTree 10 49 = (2650145469514014630216848428435665290412323195432566290594358601198437389336514863429164300707114529324288206853553029907853945050080345524324737429551933912075556356870141718880768) := by
  change 17 * certTree 9 98 + 183 * certTree 9 99 = _
  rw [certLevel9_98, certLevel9_99]
  norm_num
private theorem certLevel10_50 : certTree 10 50 = (3059726216104806195517746025057884227112251911274950915662645047152663935893653858977968233453719969418883210640655703397621227842694112923247653096934168399719391981488537419062784) := by
  change 183 * certTree 9 100 + 17 * certTree 9 101 = _
  rw [certLevel9_100, certLevel9_101]
  norm_num
private theorem certLevel10_51 : certTree 10 51 = (5408132130025342727250600943064189764976383938582033312758478501409814347228570166048785897719444079800415757181340485152930803829431732270115578698753234739669528459802569490358784) := by
  change 17 * certTree 9 102 + 183 * certTree 9 103 = _
  rw [certLevel9_102, certLevel9_103]
  norm_num
private theorem certLevel10_52 : certTree 10 52 = (5793952668969586256172944825169742483480857474125731808042435577086986272856196238419054602514149947751935579033855135180303306814053089820807035831510771396500510029370341732064768) := by
  change 183 * certTree 9 104 + 17 * certTree 9 105 = _
  rw [certLevel9_104, certLevel9_105]
  norm_num
private theorem certLevel10_53 : certTree 10 53 = (7958279590013152624001341966442070739744476529226297560354537913462837301644673174157655993707319008741809095884833210497492426732499359774212380975205696743773706131376920955773440) := by
  change 17 * certTree 9 106 + 183 * certTree 9 107 = _
  rw [certLevel9_106, certLevel9_107]
  norm_num
private theorem certLevel10_54 : certTree 10 54 = (8305513079370069729423733249085686563973545596307688640288556498037841822015880426320205566784442159796676476557572026540847192453525422040806228990483389704320418281414826126679552) := by
  change 183 * certTree 9 108 + 17 * certTree 9 109 = _
  rw [certLevel9_108, certLevel9_109]
  norm_num
private theorem certLevel10_55 : certTree 10 55 = (10202587277857941820728147100396080129924196851867438810553616768093730227016672201865525800630090808082036835235702040502545287865772248070998057948086342861329143388837689638314496) := by
  change 17 * certTree 9 110 + 183 * certTree 9 111 = _
  rw [certLevel9_110, certLevel9_111]
  norm_num
private theorem certLevel10_56 : certTree 10 56 = (10497889751835904824923876511120410089699454941624870342970168368331644593687458437560189792799520214517052691809847618979615099810112116069257369488227163471751905577415621507227136) := by
  change 183 * certTree 9 112 + 17 * certTree 9 113 = _
  rw [certLevel9_112, certLevel9_113]
  norm_num
private theorem certLevel10_57 : certTree 10 57 = (12054807852980351232714046359173926477239556402540005541963045387781548869722247354577959417215574612983271839155760068214559629058480235811491732610555652501761049590193452606874112) := by
  change 17 * certTree 9 114 + 183 * certTree 9 115 = _
  rw [certLevel9_114, certLevel9_115]
  norm_num
private theorem certLevel10_58 : certTree 10 58 = (12286831022221565028567491805205689879762377145275291807326628301282089505509661285522827047806683001595578392694345617121510161168819185920872125199682961142566549977583373384097280) := by
  change 183 * certTree 9 116 + 17 * certTree 9 117 = _
  rw [certLevel9_116, certLevel9_117]
  norm_num
private theorem certLevel10_59 : certTree 10 59 = (13443761637275743494162992015503611231074366466107157798002685182131598406171727614511434573789985537440385519669228279077851961696691900984445175021398154529684485451264371913712128) := by
  change 17 * certTree 9 118 + 183 * certTree 9 119 = _
  rw [certLevel9_118, certLevel9_119]
  norm_num
private theorem certLevel10_60 : certTree 10 60 = (13603588996520865634221822213174895936057013363250430507724733365151758238112519598501455857452081417944208963293605904952385731327657849483796322260624311777416866689431509157748224) := by
  change 183 * certTree 9 120 + 17 * certTree 9 121 = _
  rw [certLevel9_120, certLevel9_121]
  norm_num
private theorem certLevel10_61 : certTree 10 61 = (14316072005628769232610196388404976131591350519268317856955625532826982978424103210042774169590648996932911651371993190211250404649506177353800550059008114524441537842222351830802944) := by
  change 17 * certTree 9 122 + 183 * certTree 9 123 = _
  rw [certLevel9_122, certLevel9_123]
  norm_num
private theorem certLevel10_62 : certTree 10 62 = (14397561489436843193832678763438715619416040007658482722466711836632268912377767178784754735344975402651230393816502097806597912674653949905968294964621101084763231499479798515179008) := by
  change 183 * certTree 9 124 + 17 * certTree 9 125 = _
  rw [certLevel9_124, certLevel9_125]
  norm_num
private theorem certLevel10_63 : certTree 10 63 = (14638216616229149143456496171568239371399791950719948346226090544385315030377573185832734067107478973505786560600090151444161013713144487243410741094358156959722261084374607338201600) := by
  change 17 * certTree 9 126 + 183 * certTree 9 127 = _
  rw [certLevel9_126, certLevel9_127]
  norm_num
private theorem certLevel11_0 : certTree 11 0 = (2923560170256405964708790523022204791470795895032348053646249989828165704511437572261740685919110187569406794016022862973806472809077154864457268154091371541199778698537002453172057088) := by
  change 183 * certTree 10 0 + 17 * certTree 10 1 = _
  rw [certLevel10_0, certLevel10_1]
  norm_num
private theorem certLevel11_1 : certTree 11 1 = (2732929898686327806739085663859815904550877976753908691023014407584531104018022982205117484707982708820826994757106929097645699932951862548615890284250089609049573071205692106925575168) := by
  change 17 * certTree 10 2 + 183 * certTree 10 3 = _
  rw [certLevel10_2, certLevel10_3]
  norm_num
private theorem certLevel11_2 : certTree 11 2 = (2669199148043761849919807149362331756299292363003961214200897987492268223152677761741514899435848302373594450878771730584278307187562069978593794755953408416481404216619593917286675456) := by
  change 183 * certTree 10 4 + 17 * certTree 10 5 = _
  rw [certLevel10_4, certLevel10_5]
  norm_num
private theorem certLevel11_3 : certTree 11 3 = (2126238111655560785093180790509625700193595579034437053057266843977575101530327887910195333687927680603323970629212313338006469446089515948871085258164210161689167736171166599278136320) := by
  change 17 * certTree 10 6 + 183 * certTree 10 7 = _
  rw [certLevel10_6, certLevel10_7]
  norm_num
private theorem certLevel11_4 : certTree 11 4 = (2008471039089614967476083202243556175084024973666636388446603923136320822973728949969080654633388770145063477355537346802076992159052556377561766706996755452224336880595061411483055104) := by
  change 183 * certTree 10 8 + 17 * certTree 10 9 = _
  rw [certLevel10_8, certLevel10_9]
  norm_num
private theorem certLevel11_5 : certTree 11 5 = (1195839995875705548867300908986769393978428471882740778913360035541554692452747237516730157952835100366577078756094835953696603249798331109368259718012170966918409081604101551643855872) := by
  change 17 * certTree 10 10 + 183 * certTree 10 11 = _
  rw [certLevel10_10, certLevel10_11]
  norm_num
private theorem certLevel11_6 : certTree 11 6 = (1041965540723283970787081380063634006674025235033579645829512053849555785370338900018313220983254521350722848779136736553612433367150200788425690994616803486696878285803202045210883072) := by
  change 183 * certTree 10 12 + 17 * certTree 10 13 = _
  rw [certLevel10_12, certLevel10_13]
  norm_num
private theorem certLevel11_7 : certTree 11 7 = (83379994039660779406929237461136353572563270937472258540196319623508396252649807051891098669869761426063000870216862391006524033951608295479576185512910004755191483787591738816891904) := by
  change 17 * certTree 10 14 + 183 * certTree 10 15 = _
  rw [certLevel10_14, certLevel10_15]
  norm_num
private theorem certLevel11_8 : certTree 11 8 = (-83175891985532689061887543517397126552352258971212946909847417366298078659400915236611550290838324314576610111443409058235941369030633616617250849976078863710581159686574166211988480) := by
  change 183 * certTree 10 16 + 17 * certTree 10 17 = _
  rw [certLevel10_16, certLevel10_17]
  norm_num
private theorem certLevel11_9 : certTree 11 9 = (-1041780230752791346218874186697195972092301187568307025063018009661625386014110665513058563632912857241366208213596658807667999911058309583068749104785203577502499467532530038557471744) := by
  change 17 * certTree 10 18 + 183 * certTree 10 19 = _
  rw [certLevel10_18, certLevel10_19]
  norm_num
private theorem certLevel11_10 : certTree 11 10 = (-1195660969630946768814496987081561059843592176552209484320258431051642981109935903018557006543789100315535623479376274282865687589409760642988911184676820109840470435983318045656517632) := by
  change 183 * certTree 10 20 + 17 * certTree 10 21 = _
  rw [certLevel10_20, certLevel10_21]
  norm_num
private theorem certLevel11_11 : certTree 11 11 = (-2008345611100167087735548969853023620803255105969633945179335468416722954724046250640205866323599456848949286716989100104697193461293518586858374741877490023804302658469229760320730112) := by
  change 17 * certTree 10 22 + 183 * certTree 10 23 = _
  rw [certLevel10_22, certLevel10_23]
  norm_num
private theorem certLevel11_12 : certTree 11 12 = (-2126124342216468034529989328086132251171662212648014771107880909847325313997637360230012845608227159447847389929741591486395176786771032362881349189555192025662507683430697871136164864) := by
  change 183 * certTree 10 24 + 17 * certTree 10 25 = _
  rw [certLevel10_24, certLevel10_25]
  norm_num
private theorem certLevel11_13 : certTree 11 13 = (-2669166562692013393469719927656583390990459078395056303090817315062283862960783075630462818341191671670108400589905224054189169010159691018064832443151820910011551619543467286511580160) := by
  change 17 * certTree 10 26 + 183 * certTree 10 27 = _
  rw [certLevel10_26, certLevel10_27]
  norm_num
private theorem certLevel11_14 : certTree 11 14 = (-2732913004323098467456684303024098800102567179065311106227944306094843563325416543534363434625637282825733989286365481674887467498123023771978114061520393868466227955096063714948975616) := by
  change 183 * certTree 10 28 + 17 * certTree 10 29 = _
  rw [certLevel10_28, certLevel10_29]
  norm_num
private theorem certLevel11_15 : certTree 11 15 = (-2923646791850726939537129768638304383106482505769453222381026876924844584150939465779943814189183210671581640623601357804348700463370649765808138571784648783816237266779447557430801408) := by
  change 17 * certTree 10 30 + 183 * certTree 10 31 = _
  rw [certLevel10_30, certLevel10_31]
  norm_num
private theorem certLevel11_16 : certTree 11 16 = (-2923654782081407552760879920755563408343407370304422770634600820739035999550121521029547368070019877411727696316602405350661541815477201698150157353972611759701227096314596693790329856) := by
  change 183 * certTree 10 32 + 17 * certTree 10 33 = _
  rw [certLevel10_32, certLevel10_33]
  norm_num
private theorem certLevel11_17 : certTree 11 17 = (-2733012894233569989210653519439130950863740218220673113101119913057923613192493249730834068290283536905100900728741449642681492877601628504243173537191450394715275186300949803019629568) := by
  change 17 * certTree 10 34 + 183 * certTree 10 35 = _
  rw [certLevel10_34, certLevel10_35]
  norm_num
private theorem certLevel11_18 : certTree 11 18 = (-2669281205130796747767844018355622416468327365909700859952041200169176180950553404873043135574692277515989243658713897628155962727098793122064411781150056648620364422591392807519423488) := by
  change 183 * certTree 10 36 + 17 * certTree 10 37 = _
  rw [certLevel10_36, certLevel10_37]
  norm_num
private theorem certLevel11_19 : certTree 11 19 = (-2126316896429324699966368732324680885400158497856119307555589902223914380755745879174830561968214161732872765857690731823199006161951112673195361145567794627350645668161430131727758336) := by
  change 17 * certTree 10 38 + 183 * certTree 10 39 = _
  rw [certLevel10_38, certLevel10_39]
  norm_num
private theorem certLevel11_20 : certTree 11 20 = (-2008549456573717326633263275974103695680006666516461424168499845644867494763531061375637770232053910404794525229026836560032705672075256360602510762593838950306266185761420052191677440) := by
  change 183 * certTree 10 40 + 17 * certTree 10 41 = _
  rw [certLevel10_40, certLevel10_41]
  norm_num
private theorem certLevel11_21 : certTree 11 21 = (-1195916874366402014429428051959554282202795731741792716625687156263120171399559349710929260451417520978537925212241609402744869217833020534924323700347975424516762222824879372942275584) := by
  change 17 * certTree 10 42 + 183 * certTree 10 43 = _
  rw [certLevel10_42, certLevel10_43]
  norm_num
private theorem certLevel11_22 : certTree 11 22 = (-1042042246277214850334778860539779569760798575501548732060605234552694751937004646964870976282323196767681070958929879100719421751916756182960033897590713579492012597555650459630472192) := by
  change 183 * certTree 10 44 + 17 * certTree 10 45 = _
  rw [certLevel10_44, certLevel10_45]
  norm_num
private theorem certLevel11_23 : certTree 11 23 = (-83456188222357268978061082350907959061218911850051182184636943909805112172465989864693248519222189662128064662057091935744779657811450315119067691905601307206930038151677503250199552) := by
  change 17 * certTree 10 46 + 183 * certTree 10 47 = _
  rw [certLevel10_46, certLevel10_47]
  norm_num
private theorem certLevel11_24 : certTree 11 24 = (83099697824153331468739807524196795743475128335623186893181439384002290601061712874299705211268006967470110976780383958539127808598902378624715269399109885451844594081296704484504576) := by
  change 183 * certTree 10 48 + 17 * certTree 10 49 = _
  rw [certLevel10_48, certLevel10_49]
  norm_num
private theorem certLevel11_25 : certTree 11 25 = (1041703525468419424410661655006730758851586543252186261801066531559591312453020455989553279251371506083597098145076455740745897974111806925126361004519722820154753371829175352859724800) := by
  change 17 * certTree 10 50 + 183 * certTree 10 51 = _
  rw [certLevel10_50, certLevel10_51]
  norm_num
private theorem certLevel11_26 : certTree 11 26 = (1195584091451657879487671716435578077052653018761855979397792855135786722060643355591367144153113863587214965593237654316452876401424204553369298033744968010203746339608180193216001024) := by
  change 183 * certTree 10 52 + 17 * certTree 10 53 = _
  rw [certLevel10_52, certLevel10_53]
  norm_num
private theorem certLevel11_27 : certTree 11 27 = (2008267194197294538593454384606939335363678299028972009216217329027795942518320980188834716150642134595556240949612197863160189951146253571686350497338018368596680350941349247965105152) := by
  change 17 * certTree 10 54 + 183 * certTree 10 55 = _
  rw [certLevel10_54, certLevel10_55]
  norm_num
private theorem certLevel11_28 : certTree 11 28 = (2126045558086636553917208189640991796528072713160531366976912582996977291430083099101340042174976967677336263866850035432917076959244681249469458070725017007860536563700347430139425792) := by
  change 183 * certTree 10 56 + 17 * certTree 10 57 = _
  rw [certLevel10_56, certLevel10_57]
  norm_num
private theorem certLevel11_29 : certTree 11 29 = (2669084506999227664917474899525657583242569474767289837759044069451878029923090395309480586816280964378715382775272650562312581730364544040808293157310472618355892187200297407738973184) := by
  change 17 * certTree 10 58 + 183 * certTree 10 59 = _
  rw [certLevel10_58, certLevel10_59]
  norm_num
private theorem certLevel11_30 : certTree 11 30 = (2732830010459007488016966803613890550535486404302390186481871839880830468207800841096493582796771932431649738356053764839877845712002991470549336324697387002182792747483746156991575040) := by
  change 183 * certTree 10 60 + 17 * certTree 10 61 = _
  rw [certLevel10_60, certLevel10_61]
  norm_num
private theorem certLevel11_31 : certTree 11 31 = (2923552186090360627547694338375445970496234607111944753641308670845261222069517935046731164781533233996629857284697033376993630024974558313945626634666101442070148713931709717648935936) := by
  change 17 * certTree 10 62 + 183 * certTree 10 63 = _
  rw [certLevel10_62, certLevel10_63]
  norm_num
private theorem certLevel12_0 : certTree 12 0 = (581471319434589864256273121998680347216520574395736141564654993067491352693899466421385542763232870375155502215803001718866561422921301003522150207030972515393402244042768214748221224960) := by
  change 183 * certTree 11 0 + 17 * certTree 11 1 = _
  rw [certLevel11_0, certLevel11_1]
  norm_num
private theorem certLevel12_1 : certTree 12 1 = (434477959949711575120688806202421142992515961134369321350895098235264803373645525437171499355300186690759392290084972760787915130822936608279503113095258402669301567401856584261772429312) := by
  change 17 * certTree 11 2 + 183 * certTree 11 3 = _
  rw [certLevel11_2, certLevel11_3]
  norm_num
private theorem certLevel12_2 : certTree 12 2 = (387879480083286533378867341463345859738009854203001052327255638538153140375889100882126172483108341642778426694916946675992931820353189445953063722586613154194666603536165964679344633856) := by
  change 183 * certTree 11 4 + 17 * certTree 11 5 = _
  rw [certLevel11_4, certLevel11_5]
  norm_num
private theorem certLevel12_3 : certTree 12 3 = (32971953101553750134848433916469730817237507577128277291957631406544484865530675990807395813301493203931817588495010338965605265454697731475999188857348190144046972391783722972076230656) := by
  change 17 * certTree 11 6 + 183 * certTree 11 7 = _
  rw [certLevel11_6, certLevel11_7]
  norm_num
private theorem certLevel12_4 : certTree 12 4 = (-32931452156149934984046281637536005684649583580393188710573383542280179956910248802021909284982931922670745190025287057387533269020597214753125640326970892876578843170696083072270911488) := by
  change 183 * certTree 11 8 + 17 * certTree 11 9 = _
  rw [certLevel11_8, certLevel11_9]
  norm_num
private theorem certLevel12_5 : certTree 12 5 = (-387853483315056672125451910263489860624336751393830573201262784048138231393369374218473142648463115308721825068358401981968303092436679832325894067903086616223475383911585452914854410240) := by
  change 17 * certTree 11 10 + 183 * certTree 11 11 = _
  rw [certLevel11_10, certLevel11_11]
  norm_num
private theorem certLevel12_6 : certTree 12 6 = (-434456586191377878007973285809924119611251989247302660265286100858119358131900949207810218658105828597347915167171100050931533225151813669714389053222181096166435283600056654288615032832) := by
  change 183 * certTree 11 12 + 17 * certTree 11 13 = _
  rw [certLevel11_12, certLevel11_13]
  norm_num
private theorem certLevel12_7 : certTree 12 7 = (-581486883982175703882058380812219381710229940599920228501602971680858899476154003477813896385256361360936918051987261666668899132264920311266517297682437423202297295057271986163969243136) := by
  change 17 * certTree 11 14 + 183 * certTree 11 15 = _
  rw [certLevel11_14, certLevel11_15]
  norm_num
private theorem certLevel12_8 : certTree 12 8 = (-581490044322868271971822135328733329891527132475460809948850988717228289341944623593831347517748457693732883738326844823096647531151555595333612745909242608735484236792687341614964066304) := by
  change 183 * certTree 11 16 + 17 * certTree 11 17 = _
  rw [certLevel11_16, certLevel11_17]
  norm_num
private theorem certLevel12_9 : certTree 12 9 = (-434493772533789964805898826327462183108190570328134747901857652509852326754460903771835726144952960314887533294155540183324069493997733102269846089918457379831714352457595391834009974784) := by
  change 17 * certTree 11 18 + 183 * certTree 11 19 = _
  rw [certLevel11_18, certLevel11_19]
  norm_num
private theorem certLevel12_10 : certTree 12 10 = (-387895137417219105019187456386573399106888747412122916805472153409483794455518693176827509380139963460712542845520018450332647914692933263083972972460588110122831669782362818891095656448) := by
  change 183 * certTree 11 20 + 17 * certTree 11 21 = _
  rw [certLevel11_20, certLevel11_21]
  norm_num
private theorem certLevel12_11 : certTree 12 11 = (-32987200631404032678676418699392409194136636652085694784818849722890146310490355143641671075817155053220014039458255768953524847162080262777109963877767170070232411140203040908504545280) := by
  change 17 * certTree 11 22 + 183 * certTree 11 23 = _
  rw [certLevel11_22, certLevel11_23]
  norm_num
private theorem certLevel12_12 : certTree 12 12 = (32916204634783189873760632912042436521532919720706209652070334443785471491695641207819251800935360878468180977217110012005340654533499853015471031376872396980318368037973277919279659008) := by
  change 183 * certTree 11 24 + 17 * certTree 11 25 = _
  rw [certLevel11_24, certLevel11_25]
  norm_num
private theorem certLevel12_13 : certTree 12 13 = (387837826092783084513892571562474725681448230041253429336330249749395031755883676419609994506170446311969446508864072332338013659883975881025880207586521817626656191995605975662286260224) := by
  change 17 * certTree 11 26 + 183 * certTree 11 27 = _
  rw [certLevel11_26, certLevel11_27]
  norm_num
private theorem certLevel12_14 : certTree 12 14 = (434440773748841359670446171996237677679760987579421167398678751869128770840397743855806397693897561479390697794813191543783138972957973917346651810616956146950528358339568635647077464064) := by
  change 183 * certTree 11 28 + 17 * certTree 11 29 = _
  rw [certLevel11_28, certLevel11_29]
  norm_num
private theorem certLevel12_15 : certTree 12 15 = (581468160232339122137516499584142751959914201974626523086551308042656921598254396412192194062565704672721309435152471110267757671674395026451388391663752142935944691356726562998612051968) := by
  change 17 * certTree 11 30 + 183 * certTree 11 31 = _
  rw [certLevel11_30, certLevel11_31]
  norm_num
private theorem certLevel13_0 : certTree 13 0 = (113795376775675041935949691031199662971496036453703992369297080401350419200335576287545469814711718452396366574423393851485975297618588005985305040809287363162370737305658145231374615465984) := by
  change 183 * certTree 12 0 + 17 * certTree 12 1 = _
  rw [certLevel12_0, certLevel12_1]
  norm_num
private theorem certLevel13_1 : certTree 13 1 = (12627818579000207342118008211590840355100631408065492633991592402546244116782228421313898366047015064246755872508174985522585604524213905441309934844867142417669928207811242703438808985600) := by
  change 17 * certTree 12 2 + 183 * certTree 12 3 = _
  rw [certLevel12_2, certLevel12_3]
  norm_num
private theorem certLevel13_2 : certTree 13 2 = (-12619964960931401528213152014148416670904598568907073278456396517055622865801854892484052824175749502097017395936720365195379740802192847449362191334188145872213009826734335901778101776384) := by
  change 183 * certTree 12 4 + 17 * certTree 12 5 = _
  rw [certLevel12_4, certLevel12_5]
  norm_num
private theorem certLevel13_3 : certTree 13 3 = (-113797861733991577736552229547404856886363362946989547040303207532185207692378498772972716755689713215206370561355577585866244606032061249346917279380663127080849804816681736590912827052032) := by
  change 17 * certTree 12 6 + 183 * certTree 12 7 = _
  rw [certLevel12_6, certLevel12_7]
  norm_num
private theorem certLevel13_4 : certTree 13 4 = (-113799072244159323172543730812725056482988704938587618934971311027920266504401701481792343940212168083306205790114456785743195679598696136684638516030005172855732759324840905176716593704960) := by
  change 183 * certTree 12 8 + 17 * certTree 12 9 = _
  rw [certLevel12_8, certLevel12_9]
  norm_num
private theorem certLevel13_5 : certTree 13 5 = (-12630875051639662765523971380560558667344113213337771731314876107250121280563552775292493466336918753571375797594701119374150061580440553560638663921461389994940669624957324407404957945856) := by
  change 17 * certTree 12 10 + 183 * certTree 12 11 = _
  rw [certLevel12_10, certLevel12_11]
  norm_num
private theorem certLevel13_6 : certTree 13 6 = (12616908491742636183634369539465836220025144219590544665046485448952456822830324840164292986176068628063157709481420361846723571997658063079271162270938519547051416614874411445487044022272) := by
  change 183 * certTree 12 12 + 17 * certTree 12 13 = _
  rw [certLevel12_12, certLevel12_13]
  norm_num
private theorem certLevel13_7 : certTree 13 7 = (113794166476248362465563104347834164129220235750206813570616428153581405756767316188979880274245782500257641489144726469423313016456699846435497156454954896655436860610053627834746322399232) := by
  change 17 * certTree 12 14 + 183 * certTree 12 15 = _
  rw [certLevel12_14, certLevel12_15]
  norm_num
private theorem certLevel14_0 : certTree 14 0 = (21039226865791536199094799598306582609820485404964943978359222784290412863646708343783157248315043732880729932952120049575817434741113241487813091360462328879814233706468231703300014383030272) := by
  change 183 * certTree 13 0 + 17 * certTree 13 1 = _
  rw [certLevel13_0, certLevel13_1]
  norm_num
private theorem certLevel14_1 : certTree 14 1 = (-21039548101656292551768681591415611893609873594970507354109245719179838596423896808626236064302205259918415108458994944421844218497504487037125019379342550735623135448507241506467275080720384) := by
  change 17 * certTree 13 2 + 183 * certTree 13 3 = _
  rw [certLevel13_2, certLevel13_3]
  norm_num
private theorem certLevel14_2 : certTree 14 2 = (-21039955096559030407589410252198214833731782928388276384532102811932660832075091768347971329986554378055749048150055510820365360413428882423819705720155790262513086340070160162265020933087232) := by
  change 183 * certTree 13 4 + 17 * certTree 13 5 = _
  rw [certLevel13_4, certLevel13_5]
  norm_num
private theorem certLevel14_3 : certTree 14 3 = (21038819909513075146319832377824571251387730594020886142728596604737589019476534384866111070951971364224222073574669090055860582735536258970043589389862700920244819574092678888331856747438080) := by
  change 17 * certTree 13 6 + 183 * certTree 13 7 = _
  rw [certLevel13_6, certLevel13_7]
  norm_num
private theorem certLevel15_0 : certTree 15 0 = (3492506198711694151054280739436039215405780977994086123019880592299088297908141381165671763348515513698560520886435055017203238843166146912638670389515782822500411465659063296093958955722293248) := by
  change 183 * certTree 14 0 + 17 * certTree 14 1 = _
  rw [certLevel14_0, certLevel14_1]
  norm_num
private theorem certLevel15_1 : certTree 15 1 = (3492424806799389234847509350854526886830514388923221465582287430864123556418929232368582813374439335226084905645613499796276275513574844390313041861102225833942079514277767513806224428918685696) := by
  change 17 * certTree 14 2 + 183 * certTree 14 3 = _
  rw [certLevel14_2, certLevel14_3]
  norm_num
private theorem certTree_strict : 1863 * (2 * 200^15 * (certDen : ℤ)) < 2500 * (certTree 15 0 + certTree 15 1) := by
  rw [certLevel15_0, certLevel15_1]
  norm_num [certDen]

private theorem ratio_bound (a d : ℤ) (hd : 0 < d) (ha : 1863*d < 2500*a) :
    (1863/2500 : ℝ) < (((a:ℚ)/(d:ℚ) : ℚ) : ℝ) := by
  push_cast
  apply (div_lt_div_iff₀ (by norm_num) (by exact_mod_cast hd)).mpr
  exact_mod_cast (by linarith only [ha] : 1863*d < a*2500)

attribute [local irreducible] modelMean windowCos windowCertificate certTree
private theorem model_strict : (1863/2500 : ℝ) < modelMean windowCos := by
  apply lt_of_lt_of_le (b := (windowCertificate : ℝ)) _ windowCertificate_valid
  rw [windowCertificate_tree]
  have h := ratio_bound _ _ (by norm_num [certDen] : (0:ℤ) < 2*200^15*(certDen:ℤ)) certTree_strict
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] using h

theorem Conjectures.Cuts.Taskb98f3332b3a9cab8abb1dd40 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∀ (x2 : ℕ),   (2000 : ℕ) ≤ x2 →     have x4 : ℕ := (1000 : ℕ) * x2 + (1 : ℕ);     ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x4), (2 : ℕ) * ((1000 : ℕ) * x2).choose ((85 : ℕ) * x2) ≤ x5.card ∧ (745 / 1000 : ℝ) * ↑x4 * ↑x5.card < ∑ x6 ∈ x5, (x1 x4 (↑x6 / (2 : ℝ) ^ x4)).re) := by
  dsimp only
  intro t ht
  let n := 1000*t
  refine ⟨univ.map (familyWord n (85*t)), ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨⟨S,b⟩,_,rfl⟩ := mem_map.mp hw
    exact mem_range.mpr (word_lt (S.val.map Fin.valEmbedding) b n)
  · simp [Fintype.card_prod, Fintype.card_finset_len, Masks, n, Nat.mul_comm]
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,Nat.cast_ofNat, phaseTerm, n] using family_total t ht model_strict
