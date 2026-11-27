import Mathlib

/-! Based on the modulo-30 obstruction in the repository's research note
by nameoverflow (upstream #3724). We use Chebyshev's fixed-modulus
prime number theorem for moving intervals, with explicit slack. -/

namespace BeaumontRefutation
open Finset Filter
open scoped Topology

private def primes (r a b : ℕ) := (Ioc a b).filter fun p => p.Prime ∧ p ≡ r [MOD 30]

private noncomputable def th (r n : ℕ) : ℝ := ∑ p ∈ primes r 0 n, Real.log p

private theorem theta_bounds {r : ℕ} (hr : r.Coprime 30) :
    ∀ᶠ n : ℕ in atTop, (1/8-1/1000000:ℝ)*n ≤ th r n ∧
      th r n ≤ (1/8+1/1000000:ℝ)*n := by
  have lim : Tendsto (fun n : ℕ => th r n / (n:ℝ)) atTop (𝓝 (1/8:ℝ)) := by
    have h := (Chebyshev.tendsto_sum_log_prime_modEq_div_atTop hr).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, th, primes, show Nat.totient 30 = 8 by decide] using h
  filter_upwards [lim.eventually_const_lt (show (1/8-1/1000000:ℝ) < 1/8 by norm_num),
    lim.eventually_lt_const (show (1/8:ℝ) < 1/8+1/1000000 by norm_num),
    eventually_ge_atTop (1:ℕ)] with n hn1 hn2 hn
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨((lt_div_iff₀ hn').mp hn1).le, ((div_lt_iff₀ hn').mp hn2).le⟩

private theorem sum_window (r a b : ℕ) (hab : a ≤ b) :
    ∑ p ∈ primes r a b, Real.log p = th r b - th r a := by
  unfold th primes
  simp only [sum_filter]
  rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  ring

private theorem prime_window {r : ℕ} (hr : r.Coprime 30) :
    ∀ᶠ K : ℕ in atTop, ∀ a b : ℕ, K ≤ a → a ≤ b → b ≤ 2000*K →
      ((primes r a b).card : ℝ) * Real.log K ≤ ((b:ℝ)-a)/8 + (K:ℝ)/250 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (theta_bounds hr)
  filter_upwards [eventually_ge_atTop (max 1 N)] with K hK
  intro a b hKa hab hb
  have hK1 := (le_max_left 1 N).trans hK
  have ha := (hN a (((le_max_right 1 N).trans hK).trans hKa)).1
  have hb' := (hN b ((((le_max_right 1 N).trans hK).trans hKa).trans hab)).2
  have hcount : ((primes r a b).card:ℝ)*Real.log K ≤ th r b - th r a := by
    rw [← sum_window _ _ _ hab, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro p hp
    have hp' := (mem_Ioc.mp (mem_filter.mp hp).1).1
    exact Real.log_le_log (by exact_mod_cast (show 0<K by omega)) (by exact_mod_cast (hKa.trans hp'.le))
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hb'' : (b:ℝ) ≤ 2000*K := by exact_mod_cast hb
  linarith

private def rows (s : ℕ) : Finset (ℕ × ℕ) :=
  if s = 0 then {(7,19),(13,13),(19,7)} else {(11,17),(17,11),(29,29)}

private def targets (K : ℕ) := (range K).image (fun t => 1920*K+30*t+26)
private def hits (m : ℕ) := (range (m+1)).filter
  fun p => p.Prime ∧ p ≤ m ∧ (m-p).Prime ∧ m ≤ 3*p ∧ 3*p ≤ 2*m
private def boxes (K s : ℕ) (r : ℕ × ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (primes r.1 (639*K) (1301*K)).sigma (fun p =>
    primes r.2 (1920*K+s-p-1) (1950*K+s-p))

private theorem residue_coprime {p : ℕ} (h : p.Prime) (hp : 5<p) : (p%30).Coprime 30 := by
  have h30 : ¬ p ∣ 30 := by
    intro hd
    have hh : p ∈ (Nat.divisors 30) := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 30 = {1,2,3,5,6,10,15,30} by decide] at hh
    simp only [mem_insert, mem_singleton] at hh
    rcases hh with h'|h'|h'|h'|h'|h'|h'|h' <;> subst p <;> norm_num at *
  change Nat.gcd (p%30) 30 = 1
  rw [← Nat.gcd_rec 30 p, Nat.gcd_comm]
  exact h.coprime_iff_not_dvd.mpr h30

private theorem allowed {p q n s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5<p) (hq5 : 5<q) (hn : n%30=26) (hs : s=0 ∨ s=2) (he : p+q=n+s) :
    (p%30,q%30) ∈ rows s := by
  have cls : ∀ a b : Fin 30, ∀ u : Fin 3, (a:ℕ).Coprime 30 → (b:ℕ).Coprime 30 →
      (u.val=0 ∨ u.val=2) → (a.val+b.val)%30=(26+u.val)%30 → (a.val,b.val) ∈ rows u.val := by
    decide +kernel
  apply cls ⟨p%30, Nat.mod_lt _ (by decide)⟩ ⟨q%30, Nat.mod_lt _ (by decide)⟩
    ⟨s, by omega⟩ (residue_coprime hp hp5) (residue_coprime hq hq5) hs
  change (p%30+q%30)%30=(26+s)%30
  omega

private theorem count_boxes (K s : ℕ) (hK : 2≤K) (hs : s=0 ∨ s=2) :
    ∑ n ∈ targets K, (hits (n+s)).card ≤ ∑ r ∈ rows s, (boxes K s r).card := by
  rw [← card_sigma]
  apply le_trans (b := ((rows s).biUnion (boxes K s)).card) _ card_biUnion_le
  apply card_le_card_of_injOn (fun z : Σ _ : ℕ, ℕ => (⟨z.2,z.1+s-z.2⟩ : Σ _ : ℕ, ℕ))
  · intro z hz
    obtain ⟨hn,hp⟩ := mem_sigma.mp hz
    obtain ⟨t,ht,he⟩ := mem_image.mp hn
    have ht' := mem_range.mp ht
    obtain ⟨_,hp',hpz,hq',h1,h2⟩ := mem_filter.mp hp
    have hn' : z.1%30=26 := by omega
    have hadd : z.2+(z.1+s-z.2)=z.1+s := by omega
    have hr := allowed hp' hq' (by omega) (by omega) hn' hs hadd
    apply mem_biUnion.mpr
    refine ⟨_,hr,mem_sigma.mpr ⟨?_,?_⟩⟩
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by dsimp only; omega,by dsimp only; omega⟩,hp',by simp [Nat.ModEq]⟩
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by dsimp only; omega,by dsimp only; omega⟩,hq',by simp [Nat.ModEq]⟩
  · intro z hz w hw he
    obtain ⟨_,hz⟩ := mem_sigma.mp hz
    obtain ⟨_,hw⟩ := mem_sigma.mp hw
    have h1 := (mem_filter.mp hz).2.2.1
    have h2 := (mem_filter.mp hw).2.2.1
    have hp : z.2=w.2 := congrArg Sigma.fst he
    have hq : z.1+s-z.2=w.1+s-w.2 := congrArg (fun v : Σ _ : ℕ, ℕ => v.2) he
    obtain ⟨n,p⟩ := z
    obtain ⟨m,q⟩ := w
    simp only at hp hq h1 h2
    have : n=m := by omega
    cases this
    cases hp
    rfl

private theorem box_bound {s : ℕ} (hs : s=0 ∨ s=2) {r : ℕ × ℕ}
    (ha : r.1.Coprime 30) (hb : r.2.Coprime 30) :
    ∀ᶠ K : ℕ in atTop, ((boxes K s r).card : ℝ)*(Real.log K)^2 ≤
      83*(19/5:ℝ)*(K:ℝ)^2 := by
  filter_upwards [prime_window ha, prime_window hb, eventually_ge_atTop (10:ℕ)] with K h1 h2 hK
  have hK' : (10:ℝ) ≤ K := by exact_mod_cast hK
  have hnon : 0 ≤ Real.log (K:ℝ) := Real.log_nonneg (by linarith)
  have hP := h1 (639*K) (1301*K) (by omega) (by omega) (by omega)
  push_cast at hP
  let P := primes r.1 (639*K) (1301*K)
  have hw : (P.card:ℝ)*Real.log K ≤ 83*K := by dsimp [P]; linarith
  let Q := fun p => primes r.2 (1920*K+s-p-1) (1950*K+s-p)
  have hq (p : ℕ) (hp : p ∈ P) : ((Q p).card:ℝ)*Real.log K ≤ (19/5:ℝ)*K := by
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp (mem_filter.mp hp).1
    have hwidth : (1950*K+s-p) = (1920*K+s-p-1)+(30*K+1) := by omega
    have h := h2 (1920*K+s-p-1) (1950*K+s-p) (by omega) (by omega) (by omega)
    have hz : ((1950*K+s-p:ℕ):ℝ) = ((1920*K+s-p-1:ℕ):ℝ)+(30*K+1) := by exact_mod_cast hwidth
    change _ ≤ _ at h
    dsimp only [Q]
    linarith
  have hsummed := Finset.sum_le_sum hq
  simp only [sum_const, nsmul_eq_mul, ← sum_mul] at hsummed
  have htotal := mul_le_mul_of_nonneg_right hsummed hnon
  have hcap := mul_le_mul_of_nonneg_right hw (show 0 ≤ (19/5:ℝ)*K by positivity)
  unfold boxes
  rw [card_sigma, Nat.cast_sum]
  change (∑ p ∈ P, ((Q p).card:ℝ))*_ ≤ _
  nlinarith only [htotal,hcap]

private theorem shift_bound (s : ℕ) (hs : s=0 ∨ s=2) : ∀ᶠ K : ℕ in atTop,
    (∑ n ∈ targets K, ((hits (n+s)).card : ℝ))*(Real.log K)^2 ≤ 3*83*(19/5:ℝ)*(K:ℝ)^2 := by
  have hrow : ∀ r ∈ rows s, r.1.Coprime 30 ∧ r.2.Coprime 30 := by
    rcases hs with rfl|rfl <;> decide
  have hall := (Filter.eventually_all_finset (rows s)).mpr
    (fun r hr => box_bound hs (hrow r hr).1 (hrow r hr).2)
  filter_upwards [hall, eventually_ge_atTop (2:ℕ)] with K hK h2
  have hn := count_boxes K s h2 hs
  have hn' : (∑ n ∈ targets K, ((hits (n+s)).card:ℝ)) ≤
    ∑ r ∈ rows s, ((boxes K s r).card:ℝ) := by exact_mod_cast hn
  have hh := Finset.sum_le_sum hK
  have hc : (rows s).card = 3 := by rcases hs with rfl|rfl <;> decide
  rw [← sum_mul, sum_const, hc] at hh
  exact (mul_le_mul_of_nonneg_right hn' (sq_nonneg _)).trans (by simp only [nsmul_eq_mul, Nat.cast_ofNat] at hh; linarith)

private def actual (n : ℕ) : ℝ := ((hits n).card:ℝ) + (hits (n+2)).card

private theorem deficit : ∀ᶠ K : ℕ in atTop,
    ∑ n ∈ targets K, actual n ≤ (99/100:ℝ)*K*((1920*(K:ℝ))/(Real.log (1920*(K:ℝ)))^2) := by
  have ht : Tendsto (fun K : ℕ => Real.log (K:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [shift_bound 0 (Or.inl rfl), shift_bound 2 (Or.inr rfl),
    ht.eventually_ge_atTop (1000*Real.log 1920), eventually_ge_atTop (2:ℕ)] with K h0 h2 hlog hK
  simp only [Nat.add_zero] at h0
  have hK' : (1:ℝ)<K := by exact_mod_cast (show 1<K by omega)
  have hL := Real.log_pos hK'
  have hXL : 0 < Real.log (1920*(K:ℝ)) := Real.log_pos (by linarith)
  have hXL' : Real.log (1920*(K:ℝ)) ≤ (1001/1000)*Real.log K := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith
  have hsq := mul_self_le_mul_self hXL.le hXL'
  let T := ∑ n ∈ targets K, actual n
  have hT : 0 ≤ T := by unfold T actual; positivity
  have hmass : T*(Real.log K)^2 ≤ 6*83*(19/5:ℝ)*(K:ℝ)^2 := by
    unfold T actual
    rw [sum_add_distrib, add_mul]
    linarith
  have hx := mul_le_mul_of_nonneg_left hsq hT
  change T ≤ _
  rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hXL)]
  nlinarith only [hx,hmass,sq_nonneg (K:ℝ)]

private theorem obstruction : ¬ (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀,
    ∃ b : ℕ → ℝ, (∀ n ∈ (Icc X (2*X)).filter Even, (X:ℝ)/(Real.log X)^2 ≤ b n) ∧
      (∑ n ∈ (Icc X (2*X)).filter Even, (actual n-b n)^2) ≤ ε*X*((X:ℝ)/(Real.log X)^2)^2) := by
  intro h
  obtain ⟨X₀,hX₀⟩ := h (1/40000000) (by norm_num)
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp deficit
  let K := max (max K₀ X₀) 2
  have hk1 : K₀ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hk2 : X₀ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hk3 : 2 ≤ K := le_max_right _ _
  obtain ⟨b,hb,he⟩ := hX₀ (1920*K) (by omega)
  let M := (1920*(K:ℝ))/(Real.log (1920*(K:ℝ)))^2
  have hpos : (1:ℝ) < K := by exact_mod_cast (show 1<K by omega)
  have hM : 0<M := by
    have hlog : 0 < Real.log (1920*(K:ℝ)) := Real.log_pos (by linarith)
    dsimp [M]; positivity
  let E := (Icc (1920*K) (2*(1920*K))).filter Even
  have hsub : targets K ⊆ E := by
    intro n hn
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hn
    have ht' := mem_range.mp ht
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,⟨960*K+15*t+13,by omega⟩⟩
  have hcard : (targets K).card = K := by
    unfold targets
    rw [card_image_of_injective _ (by intro a b hab; dsimp only at hab; omega),card_range]
  have bfloor (n : ℕ) (hn : n ∈ targets K) : M ≤ b n := by
    simpa [M] using hb n (hsub hn)
  have hbs := sum_le_sum bfloor
  rw [sum_const,hcard,nsmul_eq_mul] at hbs
  have hdef := hK₀ K hk1
  change _ ≤ (99/100:ℝ)*K*M at hdef
  let a := M/100
  have ha : 0 ≤ 2*a := by dsimp [a]; positivity
  have hmean : (K:ℝ)*a ≤ ∑ n ∈ targets K, (b n-actual n) := by
    rw [sum_sub_distrib]
    dsimp [a]; linarith
  have htan (n : ℕ) (_ : n ∈ targets K) :
      (2*a)*(b n-actual n)-a^2 ≤ (actual n-b n)^2 := by
    nlinarith only [sq_nonneg ((b n-actual n)-a)]
  have he1 := sum_le_sum htan
  rw [sum_sub_distrib, ← mul_sum, sum_const, hcard, nsmul_eq_mul] at he1
  have he2 : (∑ n ∈ targets K, (actual n-b n)^2) ≤ ∑ n ∈ E, (actual n-b n)^2 :=
    sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  push_cast at he
  change _ ≤ 1/40000000*(1920*(K:ℝ))*M^2 at he
  have hh := (he1.trans he2).trans he
  have hmul := mul_le_mul_of_nonneg_left hmean ha
  have hcontr : (0:ℝ) < K*M^2 := mul_pos (by linarith) (sq_pos_of_pos hM)
  dsimp only [a] at hh hmul
  nlinarith only [hh,hmul,hcontr]

end BeaumontRefutation

theorem Conjectures.Goldbach.BeaumontCentralLocalPredictionRefute :
    ¬ (let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card; let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let M := fun X : ℕ => (X:ℝ)/(Real.log (X:ℝ))^2; let R := fun n : ℕ => ((H n + H (n+2)):ℝ); ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∃ b : ℕ → ℝ, (∀ n ∈ E X, M X ≤ b n) ∧ (∑ n ∈ E X, (R n-b n)^2) ≤ ε*(X:ℝ)*(M X)^2) := by
  simpa only [BeaumontRefutation.actual, BeaumontRefutation.hits, Nat.cast_add] using BeaumontRefutation.obstruction
