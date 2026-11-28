import Conjectures.Goldbach.ExceptionalZeroProgressions

/-! For a fixed finite family of moduli, remove the exceptional term using
the compact zero-free strip. Keep the threshold dependence explicit, then
reduce the fixed-modulus BMOR target to a finite initial interval. -/

namespace Conjectures.Goldbach.FixedModulusPrimeBounds

open Real DirichletCharacter ExceptionalZeroCatalogue ExceptionalZeroTwistedWindow
open ExceptionalZeroPrimeFamily ExceptionalZeroProgressions
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps (residuePrefix residueSlice)
open scoped Classical

noncomputable def progression (n q a : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range (n+1)).filter (fun j => j%q=a%q), ArithmeticFunction.vonMangoldt j

private theorem convert_prefix (n q a : ℕ) (ha : a<q) :
    progression n q a=residuePrefix ArithmeticFunction.vonMangoldt n q a := by
  classical
  have seteq : Finset.range (n+1)=insert 0 (Finset.Ioc 0 n) := by
    ext j
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Ioc]
    omega
  unfold progression residuePrefix residueSlice
  rw [Nat.mod_eq_of_lt ha,seteq,Finset.filter_insert]
  split_ifs <;> simp

private theorem exponential_budget {k C B u : ℝ} (kp : 0<k) (bp : 0<B) (up : 0<u) (m : ℕ)
    (budget : B*C*((2*m+1).factorial:ℝ)≤k^(2*m+1)*u) :
    C*exp (-(k*u))≤1/(B*(u^2)^m) := by
  have fac : 0<((2*m+1).factorial:ℝ) := by positivity
  have series := Real.pow_div_factorial_le_exp (k*u) (mul_nonneg kp.le up.le) (2*m+1)
  have enough : B*C*(u^2)^m≤exp (k*u) := by
    apply le_trans _ series
    apply (le_div_iff₀ fac).mpr
    calc
      _ = (B*C*((2*m+1).factorial:ℝ))*u^(2*m) := by rw [pow_mul];ring
      _ ≤ (k^(2*m+1)*u)*u^(2*m) := mul_le_mul_of_nonneg_right budget (by positivity)
      _ = (k*u)^(2*m+1) := by rw [mul_pow,pow_succ u];ring
  rw [Real.exp_neg,←div_eq_mul_inv]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).mpr
  linarith only [enough]

theorem fixed_bounds :
    ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ (Q : ℕ) [NeZero Q], ∃ δ : ℝ, 0<δ ∧
    ∀ n : ℕ, exp 64≤(n:ℝ) →
      let u := sqrt (log n)
      (Q:ℝ)≤exp u → k≤δ*u →
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ a : ℕ, a<q → a.Coprime q →
        let R := |progression n q a-(n:ℝ)/q.totient|
        R≤C*n*exp (-(k*u)) ∧
        ∀ (m : ℕ) (B : ℝ), 0<B → B*C*((2*m+1).factorial:ℝ)≤k^(2*m+1)*u →
          R≤(n:ℝ)/(B*(log n)^m) := by
  obtain ⟨k,C,kp,Cp,est⟩ := progressions
  refine ⟨k,C,kp,Cp,?_⟩
  intro Q _
  obtain ⟨δ,dp,strip⟩ := bounded_strip Q 0
  refine ⟨δ,dp,?_⟩
  intro n hn u hQ thin
  have pos := (Real.exp_pos 64).trans_le hn
  have logn := log_le_log (Real.exp_pos _) hn
  rw [log_exp] at logn
  have up : 0<u := Real.sqrt_pos.mpr (by linarith)
  have usq : u^2=log n := Real.sq_sqrt (by linarith)
  obtain ⟨b,d,_,family⟩ := est n hn Q hQ
  intro q _ qQ a ha cop R
  let s := 1-k/u
  have empty : carriers q s b=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
    intro χ hχ
    obtain ⟨above,below,zero⟩ := mem_carriers.mp hχ
    have lb : 1-δ≤(b:ℂ).re := by
      change 1-k/u<b at above
      change 1-δ≤b
      linarith only [above,(div_le_iff₀ up).mpr thin]
    exact strip q qQ χ (b:ℂ) (by simp) lb zero)
  have vanish : amplitude q a s b=0 := by simp [amplitude,empty]
  have raw := (family q qQ).2.2 a ha cop
  have er := raw.2.1
  change |residuePrefix ArithmeticFunction.vonMangoldt ⌊(n:ℝ)⌋₊ q a-
    ((n:ℝ)-(amplitude q a s b).re*((n:ℝ)^b/b))/q.totient|≤C*n*exp (-(k*u)) at er
  simp only [Nat.floor_natCast,vanish,Complex.zero_re,zero_mul,sub_zero] at er
  have bound : R≤C*n*exp (-(k*u)) := by simpa only [R,convert_prefix n q a ha] using er
  refine ⟨bound,?_⟩
  intro m B bp budget
  have small := exponential_budget kp bp up m budget
  rw [usq] at small
  calc
    R ≤ C*n*exp (-(k*u)) := bound
    _ = (n:ℝ)*(C*exp (-(k*u))) := by ring
    _ ≤ (n:ℝ)*(1/(B*(log n)^m)) := mul_le_mul_of_nonneg_left small pos.le
    _ = _ := by ring

/-- The remaining finite interval starts at the exact published threshold.
Its upper endpoint depends on the analytic constants and the zero-free
width; this theorem provides no numerical values for those constants. -/
theorem finite_bmor :
    ∃ N : ℕ, 8000000000≤N ∧
      (∀ (q a n : ℕ), 3≤q → q≤105 → a<q → a.Coprime q → N≤n →
        |progression n q a-(n:ℝ)/q.totient|≤(n:ℝ)/(840*log n)) ∧
      ((∀ (q a n : ℕ), 3≤q → q≤105 → a<q → a.Coprime q → 8000000000≤n →
        |progression n q a-(n:ℝ)/q.totient|≤(n:ℝ)/(840*log n)) ↔
       ∀ (q a n : ℕ), 3≤q → q≤105 → a<q → a.Coprime q → 8000000000≤n → n<N →
        |progression n q a-(n:ℝ)/q.totient|≤(n:ℝ)/(840*log n)) := by
  obtain ⟨k,C,kp,Cp,all⟩ := fixed_bounds
  obtain ⟨δ,dp,raw⟩ := all 105
  let U := max 8 (max (log 105) (max (k/δ) (5040*C/k^3)))
  have U8 : 8≤U := le_max_left ..
  have UQ : log 105≤U := (le_max_left ..).trans (le_max_right ..)
  have Ud : k/δ≤U := ((le_max_left ..).trans (le_max_right ..)).trans (le_max_right ..)
  have UB : 5040*C/k^3≤U := ((le_max_right ..).trans (le_max_right ..)).trans (le_max_right ..)
  let N := max 8000000000 ⌈exp (U^2)⌉₊
  have tail (q a n : ℕ) (q3 : 3≤q) (qQ : q≤105) (ha : a<q) (cop : a.Coprime q) (hn : N≤n) :
      |progression n q a-(n:ℝ)/q.totient|≤(n:ℝ)/(840*log n) := by
    have : NeZero q := ⟨by omega⟩
    have T : exp (U^2)≤(n:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right ..).trans hn))
    have np := (Real.exp_pos _).trans_le T
    have big : exp 64≤(n:ℝ) := (exp_le_exp.mpr (by nlinarith only [U8,sq_nonneg (U-8)] : (64:ℝ)≤U^2)).trans T
    have logn := log_le_log (exp_pos _) T
    rw [log_exp] at logn
    let u := sqrt (log n)
    have sq : u^2=log n := sq_sqrt (by nlinarith only [logn,sq_nonneg U])
    have u0 : 0≤u := sqrt_nonneg _
    have uU : U≤u := by nlinarith only [sq,logn,u0,U8]
    have Qle : ((105:ℕ):ℝ)≤exp u := by
      norm_num only [Nat.cast_ofNat]
      rw [←exp_log (by norm_num : (0:ℝ)<105)]
      exact exp_le_exp.mpr (UQ.trans uU)
    have thin := (div_le_iff₀ dp).mp (Ud.trans uU)
    have funds := (div_le_iff₀ (by positivity : 0<k^3)).mp (UB.trans uU)
    have h := (raw n big Qle (by linarith only [thin]) q qQ a ha cop).2 1 840 (by norm_num)
    norm_num at h
    exact h (by linarith only [funds])
  refine ⟨N,le_max_left ..,tail,?_⟩
  constructor
  · exact fun all q a n q3 qQ ha cop hn _ => all q a n q3 qQ ha cop hn
  · intro finite q a n q3 qQ ha cop hn
    by_cases large : N≤n
    · exact tail q a n q3 qQ ha cop large
    · exact finite q a n q3 qQ ha cop hn (lt_of_not_ge large)

end Conjectures.Goldbach.FixedModulusPrimeBounds

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.FixedModulusPrimeBounds :
by
  classical
  let ψ := fun n q a : ℕ => ∑ j ∈ (Finset.range (n+1)).filter (fun j => j%q=a%q),
    ArithmeticFunction.vonMangoldt j
  let target := fun q a n : ℕ =>
    |ψ n q a-(n:ℝ)/q.totient|≤(n:ℝ)/(840*Real.log n)
  exact (∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ (Q : ℕ) [NeZero Q], ∃ δ : ℝ, 0<δ ∧
    ∀ n : ℕ, Real.exp 64≤(n:ℝ) →
      let u := Real.sqrt (Real.log n)
      (Q:ℝ)≤Real.exp u → k≤δ*u →
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ a : ℕ, a<q → a.Coprime q →
        let R := |ψ n q a-(n:ℝ)/q.totient|
        R≤C*n*Real.exp (-(k*u)) ∧
        ∀ (m : ℕ) (B : ℝ), 0<B → B*C*((2*m+1).factorial:ℝ)≤k^(2*m+1)*u →
          R≤(n:ℝ)/(B*(Real.log n)^m)) ∧
    ∃ N : ℕ, 8000000000≤N ∧
      (∀ (q a n : ℕ), 3≤q → q≤105 → a<q → a.Coprime q → N≤n → target q a n) ∧
      ((∀ (q a n : ℕ), 3≤q → q≤105 → a<q → a.Coprime q → 8000000000≤n → target q a n) ↔
       ∀ (q a n : ℕ), 3≤q → q≤105 → a<q → a.Coprime q → 8000000000≤n → n<N → target q a n) :=
by
  with_unfolding_all exact ⟨FixedModulusPrimeBounds.fixed_bounds,FixedModulusPrimeBounds.finite_bmor⟩
