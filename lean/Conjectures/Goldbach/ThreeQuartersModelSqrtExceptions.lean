import Mathlib

/- Finite Fourier, Ramanujan sum, and major-arc arithmetic lemmas from goldbach-proofs VinogradovPolylogMinorSaving, revision 18aa6d2582c892b8185875364e6658bfb28f1b61. The underlying major-arc estimates are from DFQDZZ PR 316, revision e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0). -/
open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace GoldbachMajorArc

noncomputable section

def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The geometric sum in the rational-frequency approximation, with the same endpoints as the prime sum. -/
def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def unitMean (q a : ℕ) : ℂ :=
  (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) * ((a : ℝ) / q))) /
    (q.totient : ℂ)

def centerErrorTerm (r : ℝ) (A : ℂ) (k : ℕ) : ℂ :=
  (primeWeight k : ℂ) * phase ((k : ℝ) * r) - A

/-- The largest initial segment discrepancy at the center, through the last term k = n. -/
def prefixError (n : ℕ) (r : ℝ) (A : ℂ) : ℝ :=
  (range (n + 2)).sup' ⟨0, by simp⟩ (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖)

private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_step (k : ℕ) (β : ℝ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have shift : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase
  rw [mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-- Abel summation transports the finite initial segment discrepancies at r to a nearby frequency. -/
theorem shifted_sum_error (n : ℕ) (r β : ℝ) (A : ℂ) :
    ‖primeSum n (r + β) - A * kernel n β‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  let g := centerErrorTerm r A
  let v := fun k : ℕ => phase ((k : ℝ) * β)
  let D := prefixError n r A
  have hD : 0 ≤ D := (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) r A)
  have expand : primeSum n (r + β) - A * kernel n β = ∑ k ∈ range (n + 1), v k * g k := by
    unfold primeSum kernel
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, phase_add]
    dsimp [v, g, centerErrorTerm]
    ring
  have habel := Finset.sum_range_by_parts (M := ℂ) v g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at habel
  have hfirst : ‖v n * ∑ k ∈ range (n + 1), g k‖ ≤ D := by
    rw [norm_mul, show ‖v n‖ = 1 from norm_phase _, one_mul]
    exact prefix_le le_rfl r A
  have htail : ‖∑ i ∈ range n, (v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ ≤
      (n : ℝ) * (2 * Real.pi * |β| * D) := by
    calc
      _ ≤ ∑ i ∈ range n, ‖(v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ range n, 2 * Real.pi * |β| * D := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (phase_step i β) (prefix_le (by have := mem_range.mp hi; omega) r A)
          (norm_nonneg _) (by positivity)
      _ = _ := by simp
  rw [expand, habel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D + n * (2 * Real.pi * |β| * D) := add_le_add hfirst htail
    _ = _ := by dsimp [D]; ring

private theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_nat_mul_two_pi_mul_I k using 2
  push_cast
  ring

private theorem phase_modulo {q : ℕ} (hq : 0 < q) (k a : ℕ) :
    phase ((k : ℝ) * ((a : ℝ) / q)) = phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have harg : (k : ℝ) * ((a : ℝ) / q) =
      ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + (((k / q * a : ℕ) : ℝ)) := by
    push_cast
    nth_rw 1 [hk]
    field_simp
  rw [harg, phase_add, phase_nat, mul_one]

/-- Logarithmic prime weight in one residue class for the initial segment 0 ≤ k < m. -/
def classMass (m q b : ℕ) : ℝ := ∑ k ∈ (range m).filter (fun k => k % q = b), primeWeight k

def classError (m q b : ℕ) : ℝ :=
  classMass m q b - if b.Coprime q then (m : ℝ) / q.totient else 0

/-- Exact expansion of the initial segment discrepancy at a rational center in progression errors. -/
theorem center_prefix_eq {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k =
      ∑ b ∈ range q, (classError m q b : ℂ) * phase ((b : ℝ) * ((a : ℝ) / q)) := by
  let e := fun k : ℕ => phase ((k : ℝ) * ((a : ℝ) / q))
  have masses : (∑ k ∈ range m, (primeWeight k : ℂ) * e k) =
      ∑ b ∈ range q, (classMass m q b : ℂ) * e b := by
    symm
    calc
      _ = ∑ b ∈ range q, ∑ k ∈ (range m).filter (fun k => k % q = b),
          (primeWeight k : ℂ) * e k := by
        refine sum_congr rfl fun b _ => ?_
        rw [classMass, Complex.ofReal_sum, sum_mul]
        refine sum_congr rfl fun k hk => ?_
        have he : e k = e b := by
          dsimp [e]
          rw [phase_modulo hq k a, (mem_filter.mp hk).2]
        rw [he]
      _ = _ := sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hq)) _
  have model : (m : ℂ) * unitMean q a =
      ∑ b ∈ range q, (↑(if b.Coprime q then (m : ℝ) / q.totient else 0) : ℂ) * e b := by
    calc
      _ = ((m : ℂ) / q.totient) * ∑ b ∈ (range q).filter (fun b => b.Coprime q), e b := by
        unfold unitMean
        dsimp [e]
        ring
      _ = _ := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun b _ => ?_
        by_cases h : b.Coprime q
        · rw [ite_eq_left h, ite_eq_left h, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
        · rw [ite_eq_right h, ite_eq_right h, Complex.ofReal_zero, zero_mul]
  change (∑ k ∈ range m, ((primeWeight k : ℂ) * e k - unitMean q a)) = _
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, masses, model, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sub_mul, classError, Complex.ofReal_sub]

/-- A useful bound even without a uniform prime number theorem in progressions. -/
theorem center_prefix_bound {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ‖∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k‖ ≤
      ∑ b ∈ range q, |classError m q b| := by
  rw [center_prefix_eq hq]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b _
  rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

end

end GoldbachMajorArc
namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open scoped ComplexConjugate

noncomputable section

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

end
end GoldbachMajorArc

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachMajorArc.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachMajorArc.RamanujanCRT
namespace GoldbachMajorArc.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachMajorArc.RamanujanPower

namespace GoldbachMajorArc

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

theorem ram_unit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [ram_unit_power hp k h hc', ram_unit_power hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

theorem unitMean_eq_ram {q a : ℕ} (h : a.Coprime q) :
    unitMean q a = ram q 1 / (q.totient : ℂ) := by
  calc
    _ = ram q a / (q.totient : ℂ) := by
      apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
      apply sum_congr rfl
      intro k _
      exact congrArg phase (by ring)
    _ = _ := congrArg (fun z : ℂ => z / (q.totient : ℂ)) (ram_unit q a h)

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

theorem sum_centers_eq_coefficient (q n : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      (unitMean q a) ^ 2 * phase (-(n : ℝ) * ((a : ℝ) / q))) = coefficient q n := by
  unfold coefficient ram
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [unitMean_eq_ram (mem_filter.mp ha).2]
  congr 1
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset
noncomputable section

def badFactor (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

private theorem badFactor_nonneg (p : ℕ) : 0 ≤ badFactor p := by unfold badFactor; positivity

private theorem tail_telescope (m : ℕ) :
    ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) ≤
      4 * ((m : ℝ) + 3) / (3 * ((m : ℝ) + 4)) := by
  induction m with
  | zero =>
    have h : ∏ p ∈ range (0 + 5), (if 5 ≤ p then 1 + badFactor p else 1) = 1 :=
      prod_eq_one fun p hp => ite_eq_right (Nat.not_le.mpr (mem_range.mp hp))
    norm_num [h]
  | succ m ih =>
    rw [show m.succ + 5 = (m + 5) + 1 by omega, prod_range_succ, ite_eq_left (show 5 ≤ m + 5 by omega)]
    apply (mul_le_mul_of_nonneg_right ih (by linarith [badFactor_nonneg (m + 5)])).trans
    unfold badFactor
    push_cast
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have h₁ : 0 < (m : ℝ) + 4 := by linarith
    have h₂ : 0 < (m : ℝ) + 1 + 4 := by linarith
    rw [show (m : ℝ) + 5 - 1 = m + 4 by ring]
    field_simp
    nlinarith only [hm]

private theorem product_tail_le {s : Finset ℕ} (hs : ∀ p ∈ s, 5 ≤ p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 4 / 3 := by
  let m := s.sup id
  have hsub : s ⊆ range (m + 5) := by
    intro p hp
    have h : p ≤ m := Finset.le_sup (f := id) hp
    exact mem_range.mpr (by omega)
  calc
    _ = ∏ p ∈ s, (if 5 ≤ p then 1 + badFactor p else 1) :=
      prod_congr rfl fun p hp => (ite_eq_left (hs p hp)).symm
    _ ≤ ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) := by
      refine prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro i _
        split_ifs <;> linarith [badFactor_nonneg i]
      · intro i _ _
        split_ifs <;> linarith [badFactor_nonneg i]
    _ ≤ _ := tail_telescope m
    _ ≤ 4 / 3 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith

/-- Every finite set of odd primes has absolute Euler excess at most 2/3.
Separate p = 3 and telescope the comparison product starting at p = 5. -/
theorem product_bad_factors {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 5 / 3 := by
  have hrest : ∀ p ∈ s.erase 3, 5 ≤ p := by
    intro p hp
    obtain ⟨hne, hmem⟩ := mem_erase.mp hp
    obtain ⟨hprime, hpos⟩ := hs p hmem
    have hfour : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hprime
    omega
  have hsub : s ⊆ insert 3 (s.erase 3) := by intro p hp; by_cases p = 3 <;> simp_all
  calc
    _ ≤ ∏ p ∈ insert 3 (s.erase 3), (1 + badFactor p) :=
      prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by linarith [badFactor_nonneg p])
        (fun p _ _ => by linarith [badFactor_nonneg p])
    _ = (5 / 4) * ∏ p ∈ s.erase 3, (1 + badFactor p) := by
      rw [prod_insert (notMem_erase _ _)]
      congr 1
      norm_num [badFactor]
    _ ≤ (5 / 4) * (4 / 3) := mul_le_mul_of_nonneg_left (product_tail_le hrest) (by norm_num)
    _ = _ := by norm_num

/-- Summing the signed factors at primes away from an even target leaves at least
a third of the mass at d. The function W may already include a denominator cutoff. -/
theorem negative_factors_lower {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k) (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    {d : ℕ} (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ s.powerset, (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
  let P := s.powerset.erase ∅
  have hempty : ∅ ∈ s.powerset := mem_powerset.mpr (empty_subset _)
  have hrest : (∑ t ∈ P, ∏ p ∈ t, badFactor p) + 1 ≤ 5 / 3 := by
    have h := prod_one_add (f := badFactor) s
    rw [← sum_erase_add _ _ hempty] at h
    simp only [prod_empty] at h
    rw [← h]
    exact product_bad_factors hs
  have hterm (t : Finset ℕ) (ht : t ∈ P) :
      -(W d * ∏ p ∈ t, badFactor p) ≤ (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
    have ht' : t ⊆ s := mem_powerset.mp (mem_erase.mp ht).2
    have hprod : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (hs p (ht' hp)).1.pos
    have hle := hmono d (d * ∏ p ∈ t, p) hd (Nat.le_mul_of_pos_right d hprod)
    apply (abs_le.mp ?_).1
    rw [abs_mul, abs_of_nonneg (hnonneg _), Finset.abs_prod]
    simp_rw [abs_neg, abs_of_nonneg (badFactor_nonneg _)]
    rw [mul_comm (W d)]
    exact mul_le_mul_of_nonneg_left hle (prod_nonneg fun _ _ => badFactor_nonneg _)
  have low := sum_le_sum hterm
  simp only [sum_neg_distrib, ← mul_sum] at low
  have cap := mul_le_mul_of_nonneg_left (show (∑ t ∈ P, ∏ p ∈ t, badFactor p) ≤ 2 / 3 by linarith) (hnonneg d)
  rw [← sum_erase_add _ _ hempty]
  simp only [prod_empty, mul_one, one_mul]
  dsimp only [P] at low cap
  linarith

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset
noncomputable section

private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]

private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos, le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

private theorem signed_powerset_floor (n : ℕ) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n)
    (hG : ∀ p ∈ G, p.Prime ∧ p ∣ n) (d : ℕ) (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ (G ∪ B).powerset,
      (∏ p ∈ t, localCoefficient p n) * W (d * ∏ p ∈ t, p) := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [empty_union]
    apply (negative_factors_lower (fun p hp => (hB p hp).1) W hnonneg hmono hd).trans
    apply le_of_eq
    apply sum_congr rfl
    intro t ht
    congr 1
    apply prod_congr rfl
    intro p hp
    simp [localCoefficient, badFactor, (hB p (mem_powerset.mp ht hp)).2]
  | @insert p G hp ih =>
    have hp' := hG p (mem_insert_self _ _)
    have hG' : ∀ r ∈ G, r.Prime ∧ r ∣ n := fun r hr => hG _ (mem_insert_of_mem hr)
    have hpB : p ∉ B := fun h => (hB p h).2 hp'.2
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hsign : 0 ≤ localCoefficient p n := by
      have h : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      simp [localCoefficient, hp'.2, le_of_lt h]
    rw [insert_union, sum_powerset_insert hpGB]
    have hsecond : 0 ≤ ∑ t ∈ (G ∪ B).powerset, (∏ r ∈ insert p t, localCoefficient r n) *
        W (d * ∏ r ∈ insert p t, r) := by
      calc
        0 ≤ localCoefficient p n * (∑ t ∈ (G ∪ B).powerset, (∏ r ∈ t, localCoefficient r n) *
            W (d * p * ∏ r ∈ t, r)) :=
          mul_nonneg hsign ((div_nonneg (hnonneg _) (by norm_num)).trans (ih hG' _ (Nat.mul_pos hd hp'.1.pos)))
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro t ht
          have hpt : p ∉ t := fun h => hpGB (mem_powerset.mp ht h)
          rw [prod_insert hpt, prod_insert hpt, ← mul_assoc d, mul_assoc (localCoefficient p n)]
    linarith [ih hG' d hd]

/-- The even-target arithmetic main term retains at least one third of the q = 1
mass under every nonnegative decreasing weight supported on the denominator cutoff. -/
theorem arithmetic_floor {Q n : ℕ} (hn : Even n) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i) (hcut : ∀ q, Q < q → W q = 0) :
    W 1 / 3 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re * W q := by
  classical
  let P := (range (Q+1)).filter Nat.Prime
  let G := P.filter (fun p => p ∣ n)
  let B := P.filter (fun p => ¬ p ∣ n)
  have hGB : G ∪ B = P := by ext p; simp [G, B]; tauto
  have hB (p : ℕ) (hp : p ∈ B) : (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n := by
    have hp' := (mem_filter.mp hp)
    have hpr := (mem_filter.mp hp'.1).2
    have hne : p ≠ 2 := fun e => hp'.2 (e ▸ even_iff_two_dvd.mp hn)
    exact ⟨⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hne)⟩, hp'.2⟩
  have hG (p : ℕ) (hp : p ∈ G) : p.Prime ∧ p ∣ n :=
    ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  have h := signed_powerset_floor n W hnonneg hmono B G hB hG 1 zero_lt_one
  rw [hGB] at h
  rw [reindex_denominators Q n W hcut]
  simpa only [one_mul] using h

end
end GoldbachMajorArc


/-! Bounds for the aggregate size of the Ramanujan coefficients of DFQDZZ's PR #316.
The bound is uniform in the frequency, including when the frequency has many prime divisors. -/
namespace GoldbachMajorArc
open Finset
noncomputable section

private def parityFactor (q : ℕ) : ℝ := if Even q then 2 else 1

private lemma parityFactor_coprime {u v : ℕ} (hc : u.Coprime v) :
    parityFactor (u*v) = parityFactor u * parityFactor v := by
  have hboth (hu : Even u) (hv : Even v) : False := by
    have hd := Nat.dvd_gcd (even_iff_two_dvd.mp hu) (even_iff_two_dvd.mp hv)
    rw [hc.gcd_eq_one] at hd; omega
  by_cases hu : Even u
  · have hv : ¬ Even v := hboth hu
    simp [parityFactor, hu, hv]
  · by_cases hv : Even v <;> simp [parityFactor, Nat.even_mul, hu, hv]

private lemma coeffPrime_size (n p : ℕ) (hp : p.Prime) :
    (p : ℝ) * ‖coefficient p n‖^2 ≤ parityFactor p := by
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) - 1 := by linarith
  have h1 : ‖coefficient p n‖ ≤ 1 / ((p : ℝ) - 1) := by
    rw [coefficient_prime hp, Complex.norm_real, Real.norm_eq_abs]
    unfold localCoefficient
    split_ifs with hd
    · rw [abs_of_nonneg (by positivity)]
    · rw [abs_neg, abs_of_nonneg (by positivity)]
      apply one_div_le_one_div_of_le hp0; nlinarith
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (Nat.cast_nonneg p)
  apply h2.trans
  by_cases htwo : p = 2
  · subst p; norm_num [parityFactor]
  have hp3 : 3 ≤ (p : ℝ) := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hodd : ¬Even p := Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two htwo)
  rw [parityFactor, ite_eq_right hodd, div_pow, one_pow, ← mul_div_assoc, mul_one]
  apply (div_le_iff₀ (by positivity)).mpr; nlinarith [sq_nonneg ((p : ℝ)-3)]

/-- Even squarefree moduli can lose a factor of two at the prime 2. -/
theorem coefficient_frequency_energy (q n : ℕ) : (q : ℝ) * ‖coefficient q n‖^2 ≤ parityFactor q := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [parityFactor]
  | one => simp [coefficient_one, parityFactor]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => simpa using coeffPrime_size n p hp
      | succ j => simp only [show j+1+1 = j+2 by omega, coefficient_higher_power hp, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]; unfold parityFactor; split <;> norm_num
  | coprime u v hu hv huv iu iv =>
    rw [coefficient_mul (by omega) (by omega) huv, Nat.cast_mul, norm_mul, mul_pow, parityFactor_coprime huv]
    calc _ = ((u:ℝ) * ‖coefficient u n‖^2) * ((v:ℝ) * ‖coefficient v n‖^2) := by ring
         _ ≤ parityFactor u * parityFactor v := mul_le_mul iu iv (by positivity) (by unfold parityFactor; split <;> norm_num)

/-- Summing the absolute coefficient values costs only a square root of the cutoff. -/
theorem sum_norm_coefficient_le_sqrt (Q n : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ‖coefficient q n‖ ≤ 4 * Real.sqrt Q := by
  have hs (q : ℕ) : ‖coefficient (q+1) n‖ ≤
      4 * (Real.sqrt (q+1 : ℕ) - Real.sqrt q) := by
    let X := Real.sqrt (q+1 : ℕ)
    let Y := Real.sqrt q
    have hX : 0 < X := Real.sqrt_pos.mpr (by positivity)
    have hY : 0 ≤ Y := Real.sqrt_nonneg _
    have hXY : Y ≤ X := Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ q))
    have hX2 : X^2 = (q : ℝ) + 1 := by dsimp only [X]; push_cast; exact Real.sq_sqrt (by positivity)
    have hY2 : Y^2 = (q : ℝ) := Real.sq_sqrt (by positivity)
    have hh : (q+1 : ℝ) * ‖coefficient (q+1) n‖^2 ≤ 2 := by
      exact_mod_cast (coefficient_frequency_energy (q+1) n).trans (show parityFactor (q+1) ≤ 2 by unfold parityFactor; split <;> norm_num)
    have hb : ‖coefficient (q+1) n‖ * X ≤ 2 := by
      have : (‖coefficient (q+1) n‖ * X)^2 ≤ 2 := by rw [mul_pow, hX2, mul_comm]; exact hh
      nlinarith
    have hprod : (X-Y)*(X+Y) = 1 := by nlinarith [hX2,hY2]
    apply (le_of_mul_le_mul_right (a := X+Y) _ (by linarith : 0 < X+Y))
    change ‖coefficient (q+1) n‖ * (X+Y) ≤ 4 * (X-Y)*(X+Y)
    nlinarith [mul_le_mul_of_nonneg_left hXY (norm_nonneg (coefficient (q+1) n))]
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Q+1)]
    linarith [hs Q]

end
end GoldbachMajorArc

/-! A change-of-frequency bound for the major-arc Dirichlet kernel. The centered-square
identity uses the reflection argument from DFQDZZ, goldbach-proofs PR #316 (Apache 2.0), and the
mode integral uses the argument from TranswarpDrive's PR #158. Taking the difference of
the two exact Fourier coefficients bounds the loss on any subinterval of one period. -/
namespace GoldbachEstermannKernel
noncomputable section
open Finset MeasureTheory
open scoped ComplexConjugate

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def kernel (M : ℕ) (t : ℝ) := ∑ k ∈ range (M + 1), phase ((k : ℝ) * t)
def twisted (M n : ℕ) (t : ℝ) := kernel M t ^ 2 * phase (-(n : ℝ) * t)

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma phase_int (j : ℤ) : phase (j : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I j using 2
  push_cast; ring

private lemma centered_mode (j : ℤ) :
    (∫ t in (-(1/2) : ℝ)..1/2, phase ((j : ℝ) * t)) = if j = 0 then 1 else 0 := by
  have hp : Function.Periodic (fun t : ℝ => phase ((j : ℝ) * t)) 1 := by
    intro t; simp only [mul_add, mul_one, phase_add, phase_int, mul_one]
  have hshift := hp.intervalIntegral_add_eq (-(1/2)) 0
  norm_num only [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num, zero_add] at hshift
  rw [hshift]
  by_cases hj : j = 0
  · subst j; simp [phase]
  let c : ℂ := (j : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((j : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c; congr 1; push_cast; ring
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hj)
    (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]; rw [integral_exp_mul_complex hc]; simp [hj, c, Complex.exp_int_mul_two_pi_mul_I]

/-- The coefficient of the square of a length M+1 kernel at every n up to M. -/
theorem full_coefficient (M n : ℕ) (hn : n ≤ M) :
    (∫ t in (-(1/2) : ℝ)..1/2, twisted M n t) = (n : ℂ) + 1 := by
  let I := range (M+1)
  let f (k j : ℕ) (t : ℝ) := phase (((k : ℤ) + (j : ℤ) - n : ℤ) * (t : ℝ))
  have hcont (k j : ℕ) : Continuous (f k j) := by dsimp [f, phase]; fun_prop
  have hex (t : ℝ) : twisted M n t = ∑ k ∈ I, ∑ j ∈ I, f k j t := by
    dsimp [twisted, kernel, I]
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
    dsimp [f]; push_cast; rw [← phase_add, ← phase_add]; congr 1; ring
  have hrow (k : ℕ) : (∫ t in (-(1/2) : ℝ)..1/2, ∑ j ∈ I, f k j t) = if k ≤ n then 1 else 0 := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    simp only [f, centered_mode]
    by_cases hk : k ≤ n
    · rw [ite_eq_left hk, sum_eq_single_of_mem (n-k) (show n-k ∈ I by apply mem_range.mpr; omega)]
      · simp [show (k : ℤ) + ↑(n-k) - ↑n = 0 by omega]
      · intro j _ hdiff; simp [show (k : ℤ) + ↑j - ↑n ≠ 0 by omega]
    · rw [ite_eq_right hk]; apply sum_eq_zero; intro j _; simp [show (k : ℤ) + ↑j - ↑n ≠ 0 by omega]
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (continuous_finsetSum I fun j _ => hcont k j).intervalIntegrable _ _)]
  simp_rw [hrow]
  rw [← Finset.sum_filter]
  have hset : I.filter (fun k => k ≤ n) = range (n+1) := by ext k; simp [I]; omega
  simp [hset]

private lemma centered (M : ℕ) (t : ℝ) : twisted M M t = ((‖kernel M t‖^2 : ℝ) : ℂ) := by
  have hc (x : ℝ) : conj (phase x) = phase (-x) := by
    unfold phase; rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1; push_cast; ring
  have hsym : kernel M t * phase (-(M : ℝ) * t) = conj (kernel M t) := by
    unfold kernel; rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (M+1), conj (phase (((M-k : ℕ) : ℝ)*t)) := by
        apply sum_congr rfl
        intro k hk
        rw [hc, ← phase_add, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]; congr 1; ring
      _ = _ := by simpa only [Nat.add_sub_cancel] using
                    (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ)*t))) (M+1))
  calc
    _ = kernel M t * (kernel M t * phase (-(M : ℝ) * t)) := by dsimp [twisted]; ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma cont (M n : ℕ) : Continuous (twisted M n) := by unfold twisted kernel phase; fun_prop

set_option maxHeartbeats 1200000 in
/-- On any subinterval of the centered period, changing the target M to n costs at most M−n. -/
theorem loss_on_interval (M n : ℕ) (hn : n ≤ M) {a b : ℝ} (ha : -(1/2) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) :
    0 ≤ (∫ t in a..b, ‖kernel M t‖ ^ 2) - (∫ t in a..b, (twisted M n t).re) ∧
      (∫ t in a..b, ‖kernel M t‖ ^ 2) - (∫ t in a..b, (twisted M n t).re) ≤ (M : ℝ) - n := by
  let loss (t : ℝ) := (twisted M M t).re - (twisted M n t).re
  have hnn (t : ℝ) : 0 ≤ loss t := by
    dsimp only [loss]; rw [centered, Complex.ofReal_re]; apply sub_nonneg.mpr
    apply (Complex.re_le_norm _).trans_eq
    simp [twisted, norm_pow, norm_phase]
  have hreal (j : ℕ) : Continuous (fun t => (twisted M j t).re) := Complex.continuous_re.comp (cont M j)
  have hcont : Continuous loss := (hreal M).sub (hreal n)
  have hex (c d : ℝ) : (∫ t in c..d, loss t) =
      (∫ t in c..d, (twisted M M t).re) - (∫ t in c..d, (twisted M n t).re) :=
    intervalIntegral.integral_sub ((hreal M).intervalIntegrable c d) ((hreal n).intervalIntegrable c d)
  have hre (j : ℕ) : (∫ t in (-(1/2) : ℝ)..1/2, (twisted M j t).re) =
      (∫ t in (-(1/2) : ℝ)..1/2, twisted M j t).re :=
    intervalIntegral.intervalIntegral_re (𝕜 := ℂ) ((cont M j).intervalIntegrable _ _)
  have hwhole : (∫ t in (-(1/2) : ℝ)..1/2, loss t) = (M : ℝ) - n := by
    rw [hex, hre, hre, full_coefficient M M le_rfl, full_coefficient M n hn]; simp
  have hlocal := hex a b
  simp only [centered, Complex.ofReal_re] at hlocal
  rw [← hlocal]
  exact ⟨intervalIntegral.integral_nonneg hab (fun t _ => hnn t),
    (intervalIntegral.integral_mono_interval ha hab hb (Filter.Eventually.of_forall hnn)
      (hcont.intervalIntegrable ..)).trans_eq hwhole⟩

end
end GoldbachEstermannKernel

namespace GoldbachSqrt

noncomputable section
open Finset MeasureTheory GoldbachMajorArc

def L (n : ℕ) : ℝ := Nat.log 2 (n + 2)
def Q (n : ℕ) : ℕ := ⌊((n : ℝ) ^ (1 / 6 : ℝ)) ^ 2⌋₊
def H (n : ℕ) : ℕ := 256 * Q n * (Nat.log 2 (n + 2)) ^ 2
def center (q a : ℕ) : ℝ := (a : ℝ) / q
def width (n q : ℕ) : ℝ := (H n : ℝ) / ((q : ℝ) * n)
def model (n : ℕ) (t : ℝ) : ℂ :=
  ∑ q ∈ Icc 1 (Q n), ∑ a ∈ (range (q+1)).filter (fun a => Nat.Coprime a q),
    (Set.Icc (center q a - width n q) (center q a + width n q)).indicator
      (fun u => unitMean q a * kernel n (u - center q a)) t

def coeff (f : ℝ → ℂ) (m : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, f t * phase (-(m:ℝ)*t)

end
end GoldbachSqrt

namespace GoldbachSqrt
noncomputable section
open Filter
open scoped Topology

private theorem L_le_log {n : ℕ} (hn : 2 ≤ n) : L n ≤ 4 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) < (n:ℝ)+2 := by positivity
  have harg : (n:ℝ)+2 ≤ (n:ℝ)^2 := by nlinarith
  have hl := Real.log_le_log hx harg
  rw [Real.log_pow] at hl
  have hnat := Real.natLog_le_logb (n+2) 2
  simp only [Nat.cast_ofNat, Real.logb, Nat.cast_add] at hnat
  have htwo := Real.log_two_gt_d9
  have hlog0 := Real.log_nonneg (by linarith : 1 ≤ (n:ℝ)+2)
  have hval := (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hnat
  have hLnn : 0 ≤ L n := Nat.cast_nonneg _
  change L n * Real.log 2 ≤ _ at hval
  push_cast at hl
  nlinarith [mul_nonneg hLnn (show 0 ≤ Real.log 2 - 1/2 by linarith)]

theorem eventually_L_pow (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (L n)^k ≤ (n:ℝ)^δ := by
  have hh : 0 < δ/2 := by positivity
  have ht := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlogReal : ∀ᶠ x : ℝ in atTop, (Real.log x)^(k:ℝ) ≤ x^(δ/2) := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop (k:ℝ) hh).bound
      (by norm_num : (0:ℝ)<1), eventually_ge_atTop (1:ℝ)] with x h hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _), one_mul] using h
  have hlog := ht.eventually hlogReal
  have hc := ((tendsto_rpow_atTop hh).comp ht).eventually_ge_atTop ((4:ℝ)^k)
  filter_upwards [eventually_ge_atTop (2:ℕ), hlog, hc] with n hn hl hC
  change (Real.log (n:ℝ))^(k:ℝ) ≤ (n:ℝ)^(δ/2) at hl
  rw [Real.rpow_natCast] at hl
  change (4:ℝ)^k ≤ (n:ℝ)^(δ/2) at hC
  have hp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (4 * Real.log (n:ℝ))^k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (L_le_log hn) k
    _ = 4^k * (Real.log (n:ℝ))^k := mul_pow ..
    _ ≤ (n:ℝ)^(δ/2) * (n:ℝ)^(δ/2) :=
      mul_le_mul hC hl (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))) _) (Real.rpow_nonneg hp.le _)
    _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring

theorem eventually_geometry :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < Q n ∧ 0 < L n ∧
      2 * H n * Q n < n ∧ (1 + Real.log (Q n : ℝ) ≤ 4 * L n) ∧
      ∀ q : ℕ, 1 ≤ q → width n q ≤ 1/2 := by
  have ht := tendsto_natCast_atTop_atTop (R := ℝ)
  have hb := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/6)).comp ht).eventually_gt_atTop 512
  filter_upwards [eventually_ge_atTop (2:ℕ), eventually_L_pow 2 (by norm_num : (0:ℝ)<1/6), hb] with n hn hLsmall h512
  have hp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hpow : ((n:ℝ)^(1/6:ℝ))^2 = (n:ℝ)^(1/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
  have hq : 0 < Q n := by
    unfold Q
    apply Nat.floor_pos.mpr
    rw [hpow]
    exact Real.one_le_rpow hn1 (by norm_num)
  have hQr : (Q n:ℝ) ≤ (n:ℝ)^(1/3:ℝ) :=
    (Nat.floor_le (sq_nonneg _)).trans_eq hpow
  have hQn : (Q n:ℝ) ≤ n := hQr.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3:ℝ)≤1))
  have hlogN : 0 < Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hL1 : 1 ≤ L n := by exact_mod_cast (show 1 ≤ Nat.log 2 (n+2) by omega)
  have hL : 0 < L n := by linarith
  have hQr2 : (Q n:ℝ)^2 ≤ (n:ℝ)^(2/3:ℝ) := by
    calc
      _ ≤ ((n:ℝ)^(1/3:ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQr _
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
  change (512:ℝ) < (n:ℝ)^(1/6:ℝ) at h512
  have hsepR : (2:ℝ) * (H n:ℝ) * (Q n:ℝ) < n := by
    have hscale : ((H n:ℕ):ℝ) = 256*(Q n:ℝ)*(L n)^2 := by simp [H,L]
    calc
      _ = 512 * ((Q n:ℝ)^2 * (L n)^2) := by rw [hscale]; ring
      _ ≤ 512 * ((n:ℝ)^(2/3:ℝ) * (n:ℝ)^(1/6:ℝ)) := by
        gcongr
      _ < (n:ℝ)^(1/6:ℝ) * ((n:ℝ)^(2/3:ℝ)*(n:ℝ)^(1/6:ℝ)) :=
        mul_lt_mul_of_pos_right h512 (by positivity)
      _ = _ := by rw [← Real.rpow_add hp, ← Real.rpow_add hp]; norm_num
  have hsep : 2 * H n * Q n < n := by exact_mod_cast hsepR
  have hlogQ : 1 + Real.log (Q n : ℝ) ≤ 4 * L n := by
    have hnlog := Nat.lt_pow_succ_log_self (b:=2) (by decide) (n+2)
    have hnle : (n:ℝ) ≤ 2^(Nat.log 2 (n+2)+1) := by
      exact_mod_cast (show n ≤ 2^(Nat.log 2 (n+2)+1) by omega)
    have hh := Real.log_le_log hp hnle
    rw [Real.log_pow] at hh
    have ht' := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hQlog := Real.log_le_log (by exact_mod_cast hq) hQn
    push_cast at hh
    change Real.log (n:ℝ) ≤ (L n + 1) * Real.log 2 at hh
    nlinarith [mul_nonneg (show 0 ≤ L n + 1 by linarith) (show 0 ≤ 1-Real.log 2 by linarith)]
  refine ⟨by omega, hq, hL, hsep, hlogQ, ?_⟩
  intro q hq1
  have hhalf : 2*H n ≤ n := by
    have h := Nat.mul_le_mul_left (2*H n) (show 1≤Q n by omega)
    simpa using h.trans (Nat.le_of_lt hsep)
  have hhalfR : (2:ℝ)*(H n:ℝ) ≤ n := by exact_mod_cast hhalf
  have hqr : (1:ℝ)≤q := by exact_mod_cast hq1
  have hmul := mul_le_mul_of_nonneg_right hqr hp.le
  apply (div_le_iff₀ (by positivity : 0<(q:ℝ)*n)).2
  linarith

end
end GoldbachSqrt

namespace GoldbachSqrt
noncomputable section
open Finset MeasureTheory GoldbachMajorArc

def nums (q : ℕ) := (range (q+1)).filter (fun a => Nat.Coprime a q)
def arc (n q a : ℕ) := Set.Icc (center q a - width n q) (center q a + width n q)

-- Reduced-fraction separation, adapted from GoldbachWideArcs.reduced_centers_eq_of_common_point,
-- goldbach-proofs L_goldbach_frontier_grh_medium_zones.lean (Apache 2.0).
theorem unique_arc {n q r a b : ℕ} {t : ℝ} (hn : 2*H n*Q n<n)
    (hq : q∈Icc 1 (Q n)) (hr : r∈Icc 1 (Q n)) (ha : a∈nums q) (hb : b∈nums r)
    (hta : t∈arc n q a) (htb : t∈arc n r b) : q=r ∧ a=b := by
  obtain ⟨hq,hqB⟩ := mem_Icc.mp hq
  obtain ⟨hr,hrB⟩ := mem_Icc.mp hr
  have hca := (mem_filter.mp ha).2
  have hcb := (mem_filter.mp hb).2
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hsmall : H n*r+H n*q<n := by
    nlinarith only [hn,Nat.mul_le_mul_left (H n) hrB,Nat.mul_le_mul_left (H n) hqB]
  have hradii : (H n:ℝ)/(q*n)+H n/(r*n)<1/(q*r) := calc
    _ = ((H n:ℝ)*r+H n*q)/(q*r*n) := by field_simp
    _ < (n:ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  have ar (q a : ℕ) (h : t∈arc n q a) : |t-(a:ℝ)/q| ≤ (H n:ℝ)/(q*n) := by
    change (a:ℝ)/q - (H n:ℝ)/(q*n) ≤ t ∧ t ≤ (a:ℝ)/q + (H n:ℝ)/(q*n) at h
    rw [abs_le]
    constructor <;> linarith [h.1,h.2]
  have he : a*r = b*q := by
    by_contra hne
    have hsep : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q-b/r| := by
      rw [show (a:ℝ)/q-b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
      apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r+1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r-b*q)]
      · have hgap : (b:ℝ)*q+1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r-b*q)]
    have htriangle := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at htriangle
    linarith [ar q a hta, ar r b htb]
  have hdiv₁ : q ∣ r := hca.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv₂ : r ∣ q := hcb.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv₁ hdiv₂
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_right hq he⟩

theorem map_model {V : Type*} [AddCommMonoid V] (n : ℕ) (h : 2*H n*Q n<n)
    (t : ℝ) (g : ℂ → V) (hg : g 0=0) :
    g (model n t) = ∑ q∈Icc 1 (Q n), ∑ a∈nums q,
      (arc n q a).indicator (fun u => g (unitMean q a * kernel n (u-center q a))) t := by
  classical
  let f (q a : ℕ) := unitMean q a * kernel n (t-center q a)
  have value {W : Type*} [AddCommMonoid W] (v : ℕ → ℕ → W)
      {q a : ℕ} (hq : q∈Icc 1 (Q n)) (ha : a∈nums q) (ht : t∈arc n q a) :
      (∑ r∈Icc 1 (Q n), ∑ b∈nums r, if t∈arc n r b then v r b else 0) = v q a := by
    calc
      _ = ∑ b∈nums q, if t∈arc n q b then v q b else 0 := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => if_neg (fun htb => hrq (unique_arc h hr hq hb ha htb ht).1)
      _ = (if t∈arc n q a then v q a else 0) := by
        apply sum_eq_single_of_mem a ha
        intro b hb hba
        exact if_neg (fun htb => hba (unique_arc h hq hq hb ha htb ht).2)
      _ = _ := if_pos ht
  change g (∑ q∈Icc 1 (Q n), ∑ a∈nums q, if t∈arc n q a then f q a else 0) =
    ∑ q∈Icc 1 (Q n), ∑ a∈nums q, if t∈arc n q a then g (f q a) else 0
  by_cases hit : ∃ q∈Icc 1 (Q n), ∃ a∈nums q, t∈arc n q a
  · obtain ⟨q,hq,a,ha,ht⟩ := hit
    rw [value f hq ha ht,value (fun r b => g (f r b)) hq ha ht]
  · have vanish {W : Type*} [AddCommMonoid W] (v : ℕ → ℕ → W) :
        (∑ q∈Icc 1 (Q n), ∑ a∈nums q, if t∈arc n q a then v q a else 0) = 0 :=
      sum_eq_zero fun q hq => sum_eq_zero fun a ha =>
        if_neg (fun hta => hit ⟨q,hq,a,ha,hta⟩)
    rw [vanish f,vanish (fun q a => g (f q a)),hg]

end
end GoldbachSqrt

/- Kernel tail bounds adapted from MajorDenominatorDilation (7b62fec45f0b516900d568fbdf819753cf17373a), and finite inverse-totient sum from PacketRationalPeakExcess (420b4c57dd820f58bdd9e96bd0d4b52adf0c2ce3), which credits muxkin PR 1708 (c56bb450d43259dd871d29020d53facb6e5de557). Apache-2.0. -/
namespace GoldbachSqrt.FloorAux
noncomputable section
open Finset MeasureTheory
open scoped ComplexConjugate
private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private noncomputable def packet (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), parsevalPhase ((k : ℝ) * t)

private theorem continuous_packet (n : ℕ) : Continuous (packet n) := by
  unfold packet parsevalPhase
  fun_prop

private theorem norm_packet_neg (n : ℕ) (t : ℝ) : ‖packet n (-t)‖ = ‖packet n t‖ := by
  have h (x : ℝ) : parsevalPhase (-x) = conj (parsevalPhase x) := by
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hh : packet n (-t) = conj (packet n t) := by
    unfold packet
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_neg, h])
  rw [hh, Complex.norm_conj]

private theorem norm_packet_le_inv (n : ℕ) {t : ℝ} (ht : 0 < t) (hhalf : t ≤ 1/2) :
    ‖packet n t‖ ≤ 1 / (2 * t) := by
  let z := parsevalPhase t
  have hnorm : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
  have hp (k : ℕ) : parsevalPhase ((k : ℝ) * t) = z ^ k := by
    dsimp [z, parsevalPhase]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hgeom : packet n t * (z - 1) = z ^ (n+1) - 1 := by
    unfold packet
    simp_rw [hp]
    exact geom_sum_mul z (n+1)
  have hz' : ‖z - 1‖ = ‖2 * Real.sin (Real.pi * t)‖ := by
    dsimp [z, parsevalPhase]
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    congr 3
    ring
  have hs : 2 * t ≤ Real.sin (Real.pi * t) := by
    have hh := Real.mul_le_sin (mul_nonneg Real.pi_pos.le ht.le)
      (show Real.pi * t ≤ Real.pi / 2 by nlinarith [mul_le_mul_of_nonneg_left hhalf Real.pi_pos.le])
    calc
      2 * t = 2 / Real.pi * (Real.pi * t) := by field_simp
      _ ≤ _ := hh
  have hz : 4 * t ≤ ‖z - 1‖ := by
    rw [hz', Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hprod : ‖packet n t‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc
      _ ≤ ‖z ^ (n+1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [hnorm, one_add_one_eq_two]
  have h := (mul_le_mul_of_nonneg_left hz (norm_nonneg (packet n t))).trans hprod
  apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
  linarith

private theorem packet_tail (n : ℕ) {b : ℝ} (hb : 0 < b) (hhalf : b ≤ 1/2) :
    (∫ t in b..(1/2 : ℝ), ‖packet n t‖^2) ≤ 1/(4*b) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc b (1/2) := by
    rw [Set.uIcc_of_le hhalf]
    exact fun h => (not_le_of_gt hb) h.1
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℤ)) MeasureTheory.volume b (1/2) :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hmono :
      (∫ t in b..(1/2 : ℝ), ‖packet n t‖^2) ≤ ∫ t in b..(1/2 : ℝ), (1/4 : ℝ) * t^(-2 : ℤ) := by
    apply intervalIntegral.integral_mono_on hhalf ((continuous_packet n).norm.pow 2 |>.intervalIntegrable _ _)
      (hint.const_mul _)
    intro t ht
    have ht0 := hb.trans_le ht.1
    calc
      _ ≤ (1/(2*t))^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_packet_le_inv n ht0 ht.2) 2
      _ = _ := by rw [zpow_neg]; field_simp <;> norm_num
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul,
    integral_zpow (n := -2) (Or.inr ⟨by decide, hzero⟩)]
  norm_num [zpow_neg]
  have hh : 0 < b⁻¹ := inv_pos.mpr hb
  ring_nf
  linarith


namespace NearKernelTotient
open Finset

/-- Each divisor has totient at most that of the ambient integer. Summing over
divisors and using Gauss's identity gives a divisor-count majorant. -/
private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1 / (q.totient : ℝ) ≤ ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹) := by
  have hφ := Nat.totient_pos.mpr hq
  have hcount : q ≤ q.divisors.card * q.totient := by
    calc
      _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
      _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum (fun d hd =>
        Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
      _ = _ := by simp
  calc
    _ ≤ (q.divisors.card : ℝ) / q := (div_le_div_iff₀ (by exact_mod_cast hφ) (by exact_mod_cast hq)).mpr
      (by rw [one_mul]; exact_mod_cast hcount)
    _ = ∑ _ ∈ q.divisorsAntidiagonal, (q:ℝ)⁻¹ := by
      rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (q:ℝ)⁻¹)]; simp [div_eq_mul_inv]
    _ = _ := by
      apply sum_congr rfl
      intro ab hab
      rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul, mul_inv]

/-- A finite reciprocal-totient bound with constant one. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ)) ≤ (1 + Real.log Q)^2 := by
  let S := Icc 1 Q
  let w := fun ab : ℕ × ℕ => (ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hf := Nat.fst_mem_divisors_of_mem_antidiagonal hab
      have hs := Nat.snd_mem_divisors_of_mem_antidiagonal hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ hf,hm _ hs⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hab
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hab).2,by omega⟩
  have hsum : (∑ i ∈ S, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
    simpa only [S,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log Q
  calc
    _ ≤ ∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab :=
      sum_le_sum (fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1)
    _ = ∑ q ∈ S, ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w ab :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w ab :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ ab ∈ S ×ˢ S, w ab := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [w]; positivity)
    _ = (∑ i ∈ S, (i:ℝ)⁻¹)^2 := by rw [sq,sum_product,sum_mul_sum]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hsum 2

end NearKernelTotient


open GoldbachMajorArc

theorem truncation {n m : ℕ} (hm : m ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1/2) :
    ‖((m:ℂ) + 1) - ∫ t in -b..b, GoldbachEstermannKernel.twisted n m t‖ ≤ 1/(2*b) := by
  let f := GoldbachEstermannKernel.twisted n m
  have hf : Continuous f := by
    dsimp only [f, GoldbachEstermannKernel.twisted, GoldbachEstermannKernel.kernel,
      GoldbachEstermannKernel.phase]
    fun_prop
  have hnorm (t : ℝ) : ‖f t‖ = ‖packet n t‖^2 := by
    have he (u : ℝ) : ‖GoldbachEstermannKernel.phase u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simp only [f, GoldbachEstermannKernel.twisted, norm_mul, norm_pow, he, mul_one] <;> rfl
  have bound (u v : ℝ) (huv : u ≤ v) :
      ‖∫ t in u..v, f t‖ ≤ ∫ t in u..v, ‖packet n t‖^2 := by
    have hv := intervalIntegral.norm_integral_le_integral_norm (f := f) (μ := volume) huv
    simpa only [hnorm] using hv
  have hneg : (∫ t in (-(1/2):ℝ)..-b, ‖packet n t‖^2) =
      ∫ t in b..(1/2:ℝ), ‖packet n t‖^2 := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => ‖packet n t‖^2) (a := b) (b := (1/2 : ℝ))
    rw [← h]
    exact intervalIntegral.integral_congr fun t _ => by rw [norm_packet_neg]
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-(1/2)) (-b)) (hf.intervalIntegrable (-b) b)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-(1/2)) b) (hf.intervalIntegrable b (1/2))
  have hfull : (∫ t in (-(1/2):ℝ)..1/2, f t) = (m:ℂ)+1 :=
    GoldbachEstermannKernel.full_coefficient n m hm
  have heq : (m:ℂ)+1 - (∫ t in -b..b, f t) =
      (∫ t in (-(1/2):ℝ)..-b, f t) + ∫ t in b..(1/2:ℝ), f t := by
    rw [← hfull, ← h2, ← h1]
    abel
  change ‖(m:ℂ)+1 - (∫ t in -b..b, f t)‖ ≤ _
  rw [heq]
  have hleft := bound (-(1/2)) (-b) (neg_le_neg hb')
  rw [hneg] at hleft
  have ht := packet_tail n hb hb'
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ 1/(4*b) + 1/(4*b) := add_le_add (hleft.trans ht) ((bound _ _ hb').trans ht)
    _ = _ := by ring

theorem coefficient_cap (q m : ℕ) :
    (q.totient:ℝ) * ‖coefficient q m‖ ≤ 1 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [coefficient_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ j =>
      cases j with
      | zero =>
        simp only [pow_one, coefficient_prime hp, Complex.norm_real, Real.norm_eq_abs,
          Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
        have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
        have h : 0 < (p:ℝ)-1 := by linarith
        by_cases hd : p ∣ m
        · simp only [localCoefficient, if_pos hd, abs_of_pos (one_div_pos.mpr h)]
          exact le_of_eq (by field_simp [h.ne'] : ((p:ℝ)-1) * (1/((p:ℝ)-1)) = 1)
        · simp only [localCoefficient, if_neg hd, abs_neg,
            abs_of_pos (one_div_pos.mpr (sq_pos_of_pos h))]
          calc
            _ = 1/((p:ℝ)-1) := by field_simp [h.ne'] <;> ring
            _ ≤ 1 := (div_le_iff₀ h).2 (by linarith)
      | succ j => simp [show j+1+1 = j+2 by omega, coefficient_higher_power hp]
  | coprime u v hu hv hc ih₁ ih₂ =>
    rw [coefficient_mul (by omega) (by omega) hc, Nat.totient_mul hc, Nat.cast_mul, norm_mul]
    calc
      _ = ((u.totient:ℝ)*‖coefficient u m‖) * ((v.totient:ℝ)*‖coefficient v m‖) := by ring
      _ ≤ (1:ℝ)*1 := mul_le_mul ih₁ ih₂ (by positivity) zero_le_one
      _ = _ := by norm_num

end
end GoldbachSqrt.FloorAux

namespace GoldbachSqrt
noncomputable section
open Finset MeasureTheory GoldbachMajorArc FloorAux

theorem ideal_floor {n m : ℕ} (hn : 0<n) (hQ : 0<Q n) (hL : 0<L n)
    (hlog : 1+Real.log (Q n:ℝ) ≤ 4*L n)
    (hwidth : ∀ q ∈ Icc 1 (Q n), width n q ≤ 1/2)
    (hl : n/2<m) (hm : m≤n) (he : Even m) :
    (n:ℝ)/8 ≤ (∑ q ∈ Icc 1 (Q n), coefficient q m *
      (∫ t in -(width n q)..width n q, GoldbachEstermannKernel.twisted n m t)).re := by
  let A (q : ℕ) := ∫ t in -(width n q)..width n q, GoldbachEstermannKernel.twisted n m t
  let C := (n:ℝ)/(512 * (L n)^2)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hQ' : (0:ℝ)<Q n := by exact_mod_cast hQ
  have hHC : (H n:ℝ) = 256*(Q n:ℝ)*(L n)^2 := by simp [H,L]
  have hC : 0≤C := by dsimp [C]; positivity
  have estimate (q : ℕ) (hq : q ∈ Icc 1 (Q n)) :
      (coefficient q m).re*((m:ℝ)+1) ≤
        (coefficient q m * A q).re + (1/(q.totient:ℝ))*C := by
    obtain ⟨hq₀,hqQ⟩ := mem_Icc.mp hq
    have hq' : (0:ℝ)<q := by exact_mod_cast hq₀
    have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq₀
    have hw : 0<width n q := by unfold width; rw [hHC]; positivity
    have hs : 1/(2*width n q) ≤ C := by
      have hrat : (q:ℝ)/(Q n:ℝ) ≤ 1 := (div_le_one hQ').2 (by exact_mod_cast hqQ)
      calc
        _ = ((q:ℝ)/(Q n:ℝ))*C := by
          unfold width C
          rw [hHC]
          field_simp [hn'.ne', hq'.ne', hQ'.ne', hL.ne'] <;> ring
        _ ≤ 1*C := mul_le_mul_of_nonneg_right hrat hC
        _ = _ := one_mul _
    have hc : ‖coefficient q m‖ ≤ 1/(q.totient:ℝ) := by
      apply (le_div_iff₀ hφ).2
      simpa only [mul_comm] using coefficient_cap q m
    have hdiff : ‖((m:ℂ)+1)-A q‖ ≤ C := (truncation hm hw (hwidth q hq)).trans hs
    have hd := (Complex.re_le_norm (coefficient q m * (((m:ℂ)+1)-A q))).trans
      (le_of_eq (norm_mul _ _))
    have hprod := mul_le_mul hc hdiff (norm_nonneg _) (by positivity : 0 ≤ 1/(q.totient:ℝ))
    have h := hd.trans hprod
    rw [mul_sub, Complex.sub_re] at h
    have hre : (coefficient q m * ((m:ℂ)+1)).re = (coefficient q m).re*((m:ℝ)+1) := by
      simp [Complex.mul_re]
    rw [hre] at h
    linarith
  let W (q : ℕ) : ℝ := if q ≤ Q n then 1 else 0
  have hb : (1/3:ℝ) ≤ ∑ q ∈ Icc 1 (Q n), (coefficient q m).re := by
    have hbase := arithmetic_floor (Q := Q n) he W
      (fun k => by dsimp [W]; split <;> norm_num)
      (fun i j _ hij => by
        by_cases hj : j ≤ Q n
        · simp [W,hj,hij.trans hj]
        · by_cases hi : i ≤ Q n <;> simp [W,hj,hi])
      (fun q hq => by simp [W, not_le_of_gt hq])
    have hself : W 1 = 1 := if_pos hQ
    rw [hself] at hbase
    refine hbase.trans_eq (sum_congr rfl fun q hq => ?_)
    simp [W, (mem_Icc.mp hq).2]
  have htot := NearKernelTotient.sum_inv_totient_le (Q n)
  have hsq := pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg (Q n)] :
      0≤1+Real.log (Q n:ℝ)) hlog 2
  have htail : (∑ q ∈ Icc 1 (Q n), 1/(q.totient:ℝ))*C ≤ (n:ℝ)/32 := by
    calc
      _ ≤ (4*L n)^2*C := mul_le_mul_of_nonneg_right (htot.trans hsq) hC
      _ = _ := by dsimp [C]; field_simp [hL.ne'] <;> ring
  have hsum := sum_le_sum estimate
  rw [← sum_mul, sum_add_distrib, ← sum_mul, ← Complex.re_sum] at hsum
  have hmul := mul_le_mul_of_nonneg_right hb (by positivity : 0≤(m:ℝ)+1)
  have hnm : (n:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast (show n ≤ 2*m by omega)
  change (n:ℝ)/8 ≤ (∑ q ∈ Icc 1 (Q n), coefficient q m * A q).re
  linarith only [htail, hsum, hmul, hnm]

end
end GoldbachSqrt

/- The clipped window and endpoint arguments are adapted from MajorDenominatorDilation,
revision 7b62fec45f0b516900d568fbdf819753cf17373a (Apache-2.0). The frequency m
is independent of the kernel length n here. -/
namespace GoldbachSqrt
noncomputable section
open Finset MeasureTheory GoldbachMajorArc

private def clipL (n q a : ℕ) := max (center q a - width n q) 0 - center q a
private def clipR (n q a : ℕ) := min (center q a + width n q) 1 - center q a
private def wave (n m q a : ℕ) (t : ℝ) :=
  (unitMean q a * GoldbachMajorArc.kernel n (t-center q a))^2 * phase (-(m:ℝ)*t)
private def amplitude (m q a : ℕ) := (unitMean q a)^2 * phase (-(m:ℝ)*center q a)
private def modelPiece (n m q a : ℕ) := amplitude m q a *
  ∫ t in clipL n q a..clipR n q a, GoldbachEstermannKernel.twisted n m t

private theorem phase_plus (u v : ℝ) : phase (u+v) = phase u * phase v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem clip_integral (n q a : ℕ) (hq : 0<q) (ha : a≤q) (F : ℝ → ℂ) :
    (∫ t in (0:ℝ)..1, (arc n q a).indicator F t) =
      ∫ β in clipL n q a..clipR n q a, F (center q a+β) := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hc : 0 ≤ center q a ∧ center q a ≤ 1 :=
    ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩
  have hw : 0 ≤ width n q := by unfold width; positivity
  have ho : max (center q a-width n q) 0 ≤ min (center q a+width n q) 1 :=
    max_le (le_min (by linarith) (by linarith [hc.2]))
      (le_min (by linarith [hc.1]) zero_le_one)
  rw [intervalIntegral.integral_comp_add_left]
  unfold clipL clipR
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    arc, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le ho, ← integral_Icc_eq_integral_Ioc]

private theorem one_piece (n m q a : ℕ) (hq : 0<q) (ha : a≤q) :
    (∫ t in (0:ℝ)..1, (arc n q a).indicator (wave n m q a) t) =
      modelPiece n m q a := by
  rw [clip_integral n q a hq ha]
  have h (β : ℝ) : wave n m q a (center q a+β) =
      amplitude m q a * GoldbachEstermannKernel.twisted n m β := by
    change (unitMean q a * GoldbachMajorArc.kernel n (center q a+β-center q a))^2 *
        phase (-(m:ℝ)*(center q a+β)) =
      ((unitMean q a)^2 * phase (-(m:ℝ)*center q a)) *
        ((GoldbachMajorArc.kernel n β)^2 * phase (-(m:ℝ)*β))
    rw [show center q a+β-center q a=β by ring, mul_add, phase_plus]
    ring
  simp_rw [h]
  simp only [intervalIntegral.integral_const_mul, modelPiece]

private theorem interior_num {q a : ℕ} (hq : 1<q) (ha : a∈nums q) : 0<a ∧ a<q := by
  obtain ⟨ha',hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp ha')
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem width_unit {n q : ℕ} (hn : 0<n) (hH : H n≤n) (hq : 0<q) :
    width n q ≤ 1/(q:ℝ) := by
  have hq' : 0<(q:ℝ) := by exact_mod_cast hq
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hh : (H n:ℝ) ≤ n := by exact_mod_cast hH
  unfold width
  apply (div_le_div_iff₀ (mul_pos hq' hn') hq').2
  nlinarith [mul_le_mul_of_nonneg_right hh hq'.le]

private theorem uncut_pair {n q a : ℕ} (hn : 0<n) (hH : H n≤n) (hq : 1<q) (ha : a∈nums q) :
    clipL n q a = -width n q ∧ clipR n q a = width n q := by
  obtain ⟨ha₁,haq⟩ := interior_num hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_unit hn hH (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a := div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast Nat.succ_le_of_lt haq
  unfold clipL clipR
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring

private theorem phase_integer_neg (m : ℕ) : phase (-(m:ℝ)) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I (-(m:ℤ)) using 2
  push_cast
  ring

private theorem endpoint_sum {n : ℕ} (m : ℕ) (hn : 0<n) (hH : H n≤n) :
    (∑ a∈nums 1, modelPiece n m 1 a) =
      ∫ t in -(width n 1)..width n 1, GoldbachEstermannKernel.twisted n m t := by
  let b := width n 1
  have hb : 0≤b := by unfold b width; positivity
  have hb' : b≤1 := by simpa [b] using width_unit hn hH (by decide : 0<1)
  have h₀ : clipL n 1 0 = 0 ∧ clipR n 1 0 = b := by
    change max (0/(1:ℝ)-b) 0 - 0/1 = 0 ∧ min (0/1+b) 1 - 0/1 = b
    simp [hb,hb']
  have h₁ : clipL n 1 1 = -b ∧ clipR n 1 1 = 0 := by
    change max (1/(1:ℝ)-b) 0 - 1/1 = -b ∧ min (1/1+b) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hu (a : ℕ) : unitMean 1 a=1 := by rw [unitMean_eq_ram (by simp), ram_one]; simp
  have hz : phase 0=1 := by simp [phase]
  have hc : Continuous (GoldbachEstermannKernel.twisted n m) := by
    unfold GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-b) 0) (hc.intervalIntegrable 0 b)
  have hnset : nums 1 = {0,1} := by decide
  rw [hnset]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}), sum_singleton, modelPiece, amplitude,
    h₀.1, h₀.2, h₁.1, h₁.2, hu, center, Nat.cast_zero, Nat.cast_one, div_one, mul_zero,
    mul_one, one_pow, one_mul, phase_integer_neg, hz]
  rw [add_comm]
  exact hadd

private theorem row_coefficient {n q : ℕ} (m : ℕ) (hn : 0<n) (hH : H n≤n) (hq : 0<q) :
    (∑ a∈nums q, modelPiece n m q a) =
      coefficient q m * ∫ t in -(width n q)..width n q, GoldbachEstermannKernel.twisted n m t := by
  rcases eq_or_lt_of_le (show 1≤q by omega) with h | h
  · subst q
    rw [coefficient_one, one_mul]
    exact endpoint_sum m hn hH
  · have hs : nums q = (range q).filter (fun a => a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (interior_num h ha).2,(mem_filter.mp ha).2⟩
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ha).1; omega),
          (mem_filter.mp ha).2⟩
    rw [← sum_centers_eq_coefficient, ← hs, sum_mul]
    apply sum_congr rfl
    intro a ha
    have hu := uncut_pair hn hH h ha
    simp only [modelPiece, amplitude, hu.1, hu.2, center]

theorem model_coefficient {n : ℕ} (m : ℕ) (hsep : 2*H n*Q n<n) (hq0 : 0<Q n) :
    coeff (fun t => model n t ^ 2) m = ∑ q∈Icc 1 (Q n), coefficient q m *
      ∫ t in -(width n q)..width n q, GoldbachEstermannKernel.twisted n m t := by
  classical
  have hn : 0<n := by omega
  have hH : H n ≤ n := by
    have h := Nat.le_mul_of_pos_right (2*H n) hq0
    omega
  have hi (q a : ℕ) :
      IntervalIntegrable ((arc n q a).indicator (wave n m q a)) volume (0:ℝ) 1 := by
    have hc : Continuous (wave n m q a) := by
      unfold wave GoldbachMajorArc.kernel phase
      fun_prop
    have hf := hc.intervalIntegrable (μ := volume) 0 1
    exact ⟨hf.1.indicator measurableSet_Icc, hf.2.indicator measurableSet_Icc⟩
  have hsplit (t : ℝ) : model n t ^ 2 * phase (-(m:ℝ)*t) =
      ∑ q∈Icc 1 (Q n), ∑ a∈nums q, (arc n q a).indicator (wave n m q a) t := by
    rw [map_model n hsep t (fun z => z^2*phase (-(m:ℝ)*t)) (by simp)]
    refine sum_congr rfl fun q _ => sum_congr rfl fun a _ => ?_
    by_cases ht : t∈arc n q a <;> simp [ht,wave]
  unfold coeff
  simp_rw [hsplit]
  rw [intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun q hq => ?_
    rw [intervalIntegral.integral_finsetSum (fun a _ => hi q a)]
    calc
      _ = ∑ a∈nums q, modelPiece n m q a := sum_congr rfl fun a ha =>
        one_piece n m q a (mem_Icc.mp hq).1 (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1))
      _ = _ := row_coefficient m hn hH (mem_Icc.mp hq).1
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ => (hi q a).1),
      integrable_finsetSum _ (fun a _ => (hi q a).2)⟩

end
end GoldbachSqrt

/- The finite Parseval proof below is adapted from Clrs17’s L-goldbach-continuous-parseval,
   PR #138, commit 5ab2bcbb94ec2a8224686cc2cf35f1736f882a64 (Apache-2.0).
   https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/138
   The application after the finite Parseval helper is new. -/

open scoped BigOperators ComplexConjugate

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

namespace GoldbachSqrt

theorem realWeightParseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _




end GoldbachSqrt

namespace GoldbachSqrt
noncomputable section
open Finset MeasureTheory Filter GoldbachMajorArc
open scoped Topology

private theorem kernel_bound (n : ℕ) (t : ℝ) : ‖kernel n t‖ ≤ (n:ℝ)+1 := by
  unfold kernel
  calc
    _ ≤ ∑ k ∈ range (n+1), ‖phase ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = _ := by simp [phase,Complex.norm_exp_ofReal_mul_I]

theorem model_memLp (n : ℕ) (p : ℝ≥0∞) :
    MemLp (model n) p (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  unfold model
  apply memLp_finsetSum
  intro q _
  apply memLp_finsetSum
  intro a _
  apply MemLp.indicator measurableSet_Icc.nullMeasurableSet
  apply MemLp.of_bound (C:=‖unitMean q a‖*((n:ℝ)+1))
  · exact (show Continuous (fun t : ℝ => unitMean q a * kernel n (t-center q a)) from by
      unfold kernel phase; fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (kernel_bound n _) (norm_nonneg _)

private theorem phase_add_energy (u v : ℝ) : phase (u+v)=phase u * phase v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem shifted_kernel_energy (n : ℕ) (c : ℝ) :
    (∫ t in (0:ℝ)..1, ‖kernel n (t-c)‖^2) = (n:ℝ)+1 := by
  have per : Function.Periodic (fun t => ‖kernel n t‖^2) 1 := by
    intro t
    have hp : kernel n (t+1)=kernel n t := by
      unfold kernel
      apply sum_congr rfl
      intro k _
      rw [mul_add, mul_one, phase_add_energy]
      have hz : phase (k:ℝ) = 1 := by
        unfold phase
        have h : (((2*Real.pi*(k:ℝ):ℝ):ℂ)*Complex.I) =
            ((k:ℤ):ℂ) * (2*(Real.pi:ℂ)*Complex.I) := by push_cast; ring
        rw [h, Complex.exp_int_mul_two_pi_mul_I]
      rw [hz,mul_one]
    change ‖kernel n (t+1)‖^2=_
    rw [hp]
  have hz : (∫ t in (0:ℝ)..1, ‖kernel n t‖^2) = (n:ℝ)+1 := by
    have hf := realWeightParseval n (fun _ => (1:ℝ))
    simpa [kernel, phase] using hf
  rw [intervalIntegral.integral_comp_sub_right (f := fun t => ‖kernel n t‖^2) c]
  simpa only [zero_sub,zero_add,show (1:ℝ)-c = -c+1 by ring] using
    (per.intervalIntegral_add_eq (-c) 0).trans (by simpa using hz)

private theorem mean_bound {q a : ℕ} (ha : a.Coprime q) :
    ‖unitMean q a‖ ≤ 1/(q.totient:ℝ) := by
  have hram (k : ℕ) : ‖ram k 1‖ ≤ 1 := by
    induction k using Nat.recOnPrimeCoprime with
    | zero => simp [ram]
    | prime_pow p k hp =>
      cases k with
      | zero => simp [ram_one]
      | succ j =>
        rw [GoldbachMajorArc.ram_unit_power hp j 1 (by simp)]
        split <;> simp
    | coprime q r hq hr hqr ihq ihr =>
      rw [ram_mul (by omega) (by omega) hqr,norm_mul]
      simpa using mul_le_mul ihq ihr (norm_nonneg _) zero_le_one
  rw [unitMean_eq_ram ha,norm_div,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (hram _) (Nat.cast_nonneg _)

private theorem nums_card {q : ℕ} (hq : 0<q) : (nums q).card ≤ 2*q.totient := by
  have hstd : ((range q).filter (fun a => a.Coprime q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp only [mem_filter,mem_range]
    exact and_congr_right fun _ => Nat.coprime_comm
  have hpos := Nat.totient_pos.mpr hq
  unfold nums
  rw [range_add_one,filter_insert]
  split
  · exact (card_insert_le ..).trans (by omega)
  · omega

private theorem piece_int (n q a : ℕ) :
    IntervalIntegrable ((arc n q a).indicator (fun t => ‖unitMean q a * kernel n (t-center q a)‖^2))
      volume 0 1 := by
  have hc : Continuous (fun t : ℝ => ‖unitMean q a * kernel n (t-center q a)‖^2) := by
    unfold kernel phase; fun_prop
  exact ⟨(hc.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
    (hc.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩

private theorem energy_split (n : ℕ) (h : 2*H n*Q n<n) :
    (∫ t in (0:ℝ)..1, ‖model n t‖^2) =
      ∑ q∈Icc 1 (Q n), ∑ a∈nums q, ∫ t in (0:ℝ)..1,
        (arc n q a).indicator (fun u => ‖unitMean q a * kernel n (u-center q a)‖^2) t := by
  have hp (t : ℝ) := map_model n h t (fun z => ‖z‖^2) (by simp)
  simp_rw [hp]
  have hi (q : ℕ) : IntervalIntegrable
      (fun t => ∑ a∈nums q,
        (arc n q a).indicator (fun u => ‖unitMean q a * kernel n (u-center q a)‖^2) t)
      volume 0 1 := by
    simpa only [Finset.sum_apply] using
      IntervalIntegrable.sum (nums q) (fun a _ => piece_int n q a)
  rw [intervalIntegral.integral_finsetSum (fun q _ => hi q)]
  apply sum_congr rfl
  intro q _
  exact intervalIntegral.integral_finsetSum (fun a _ => piece_int n q a)

private theorem piece_bound {n q a : ℕ} (hq : 0<q) (ha : a∈nums q) :
    (∫ t in (0:ℝ)..1,
      (arc n q a).indicator (fun u => ‖unitMean q a * kernel n (u-center q a)‖^2) t) ≤
      ((n:ℝ)+1)/(q.totient:ℝ)^2 := by
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hc : Continuous (fun t : ℝ => ‖unitMean q a‖^2 * ‖kernel n (t-center q a)‖^2) := by
    unfold kernel phase; fun_prop
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖unitMean q a‖^2 * ‖kernel n (t-center q a)‖^2 := by
      apply intervalIntegral.integral_mono_on zero_le_one (piece_int ..) (hc.intervalIntegrable _ _)
      intro t _
      by_cases hit : t∈arc n q a
      · simp [Set.indicator_of_mem hit,norm_mul,mul_pow]
      · rw [Set.indicator_of_notMem hit]; positivity
    _ = ‖unitMean q a‖^2 * ((n:ℝ)+1) := by
      rw [intervalIntegral.integral_const_mul,shifted_kernel_energy]
    _ ≤ (1/(q.totient:ℝ))^2 * ((n:ℝ)+1) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (mean_bound (mem_filter.mp ha).2) 2)
        (by positivity)
    _ = _ := by rw [div_pow,one_pow]; ring

theorem model_energy (n : ℕ) (h : 2*H n*Q n<n) :
    (∫ t in (0:ℝ)..1, ‖model n t‖^2) ≤ 2*((n:ℝ)+1)*(1+Real.log (Q n))^2 := by
  rw [energy_split n h]
  calc
    _ ≤ ∑ q∈Icc 1 (Q n), (2*((n:ℝ)+1))*(1/(q.totient:ℝ)) := by
      apply sum_le_sum
      intro q hq
      have hq0 : 0<q := (mem_Icc.mp hq).1
      have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      calc
        _ ≤ ∑ _a∈nums q, ((n:ℝ)+1)/(q.totient:ℝ)^2 := sum_le_sum (fun a ha => piece_bound hq0 ha)
        _ = ((nums q).card:ℝ)*(((n:ℝ)+1)/(q.totient:ℝ)^2) := by simp
        _ ≤ (2*(q.totient:ℝ))*(((n:ℝ)+1)/(q.totient:ℝ)^2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast nums_card hq0) (by positivity)
        _ = _ := by field_simp <;> ring
    _ = (2*((n:ℝ)+1))* ∑ q∈Icc 1 (Q n), 1/(q.totient:ℝ) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (FloorAux.NearKernelTotient.sum_inv_totient_le _) (by positivity)

theorem prime_energy (n : ℕ) :
    (∫ t in (0:ℝ)..1, ‖primeSum n t‖^2) ≤ ((n:ℝ)+1)*(Real.log n)^2 := by
  have hf := realWeightParseval n primeWeight
  change (∫ t in (0:ℝ)..1, ‖primeSum n t‖^2) = ∑ k∈range (n+1), (primeWeight k)^2 at hf
  rw [hf]
  calc
    _ ≤ ∑ _k ∈ range (n+1), (Real.log n)^2 := by
      apply sum_le_sum
      intro k hk
      by_cases hp : k.Prime
      · rw [primeWeight, if_pos hp]
        exact pow_le_pow_left₀ (Real.log_natCast_nonneg k)
          (Real.log_le_log (by exact_mod_cast hp.pos)
            (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk))) 2
      · simp [primeWeight,hp,sq_nonneg]
    _ = _ := by simp

theorem prime_memLp (n : ℕ) (p : ℝ≥0∞) :
    MemLp (primeSum n) p (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  unfold primeSum
  apply memLp_finsetSum
  intro k _
  apply MemLp.of_bound (C:=‖(primeWeight k:ℂ)‖)
  · exact (show Continuous (fun t : ℝ => (primeWeight k:ℂ)*phase ((k:ℝ)*t)) from by
      unfold phase; fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      simp only [norm_mul,phase,Complex.norm_exp_ofReal_mul_I,mul_one,le_rfl]

theorem energy_of_geometry (geo : ∀ᶠ n : ℕ in atTop, 2*H n*Q n<n ∧ Q n≤n)
    (η : ℝ) (hη : 0<η) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ t in (0:ℝ)..1, ‖primeSum n t + model n t‖^2) ≤ C*(n:ℝ)^(1+η) := by
  refine ⟨36, by norm_num, ?_⟩
  have hlog : ∀ᶠ x : ℝ in atTop, (Real.log x)^(2:ℝ) ≤ x^η := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop 2 hη).bound (by norm_num : (0:ℝ)<1),
      eventually_ge_atTop (1:ℝ)] with x hx hx1
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using hx
  have hlognat := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hlog
  have hlog1 := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (1:ℝ)
  filter_upwards [geo,hlognat,hlog1,eventually_ge_atTop (1:ℕ)] with n hgeo hpower hl hn
  change (Real.log (n:ℝ))^(2:ℝ) ≤ (n:ℝ)^η at hpower
  have hpw : (Real.log (n:ℝ))^2 ≤ (n:ℝ)^η := by simpa using hpower
  change 1 ≤ Real.log (n:ℝ) at hl
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have hqlog : Real.log (Q n:ℝ) ≤ Real.log (n:ℝ) := by
    by_cases hq : Q n=0
    · simp [hq, Real.log_nonneg hnr]
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hq) (by exact_mod_cast hgeo.2)
  let S := primeSum n
  let M := model n
  have hiS : IntervalIntegrable (fun t => ‖S t‖^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      ((prime_memLp n 2).integrable_norm_pow (by decide : (2:ℕ) ≠ 0))
  have hiM : IntervalIntegrable (fun t => ‖M t‖^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      ((model_memLp n 2).integrable_norm_pow (by decide : (2:ℕ) ≠ 0))
  have hi : IntervalIntegrable (fun t => ‖S t+M t‖^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (((prime_memLp n 2).add (model_memLp n 2)).integrable_norm_pow (by decide : (2:ℕ) ≠ 0))
  have hpt := intervalIntegral.integral_mono_on zero_le_one hi
    ((hiS.add hiM).const_mul 2) (fun t _ => show ‖S t+M t‖^2≤2*(‖S t‖^2+‖M t‖^2) by
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (S t) (M t)) 2
      nlinarith only [h,sq_nonneg (‖S t‖-‖M t‖)])
  change (∫ t in (0:ℝ)..1, ‖S t+M t‖^2) ≤ ∫ t in (0:ℝ)..1, 2*(‖S t‖^2+‖M t‖^2) at hpt
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hiS hiM] at hpt
  have hsq : (1+Real.log (Q n:ℝ))^2 ≤ 4*(Real.log (n:ℝ))^2 := by
    have h := pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg (Q n)] : 0≤1+Real.log (Q n:ℝ))
      (by linarith : 1+Real.log (Q n:ℝ) ≤ 2*Real.log (n:ℝ)) 2
    nlinarith only [h]
  have hrel := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤2*((n:ℝ)+1))
  have hmass := mul_le_mul (by linarith : (n:ℝ)+1≤2*n) hpw (sq_nonneg _) (by positivity)
  have hpos : 0<(n:ℝ) := by linarith
  rw [Real.rpow_add hpos,Real.rpow_one]
  dsimp only [S,M] at hpt
  nlinarith only [hpt,prime_energy n,model_energy n hgeo.1,hrel,hmass]

end
end GoldbachSqrt

namespace GoldbachSqrt
noncomputable section
open Finset MeasureTheory Filter GoldbachMajorArc
open scoped Topology

private abbrev μ01 := volume.restrict (Set.Ioc (0:ℝ) 1)

private theorem continuous_memLp {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 μ01 := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2
  exact ((hf.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1

private theorem model_memLp_two (n : ℕ) : MemLp (model n) 2 μ01 := by
  classical
  unfold model
  refine memLp_finsetSum _ fun q _ => memLp_finsetSum _ fun a _ => ?_
  apply MemLp.indicator measurableSet_Icc.nullMeasurableSet
  apply continuous_memLp
  unfold kernel phase
  fun_prop

private theorem phase_cont (m : ℕ) : Continuous (fun t : ℝ => phase (-(m:ℝ)*t)) := by
  unfold phase
  fun_prop

-- Interval Parseval, restricted to the nonnegative Fourier modes in a finite range.
private theorem bessel {f : ℝ → ℂ} (M : ℕ) (hf : MemLp f 2 μ01) :
    ∑ m ∈ range M, ‖coeff f m‖^2 ≤ ∫ t in (0:ℝ)..1, ‖f t‖^2 := by
  have hco (m : ℕ) : fourierCoeffOn zero_lt_one f (m:ℤ) = coeff f m := by
    rw [fourierCoeffOn_eq_integral, sub_zero, one_div_one, one_smul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [smul_eq_mul, fourier_coe_apply]
    rw [mul_comm]
    congr 2
    unfold phase
    push_cast
    ring
  let s : Finset ℤ := (range M).map ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have hp := hasSum_sq_fourierCoeffOn zero_lt_one hf
  have hb := sum_le_hasSum s (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one f i‖) hp
  simp only [s, Finset.sum_map, sub_zero, inv_one, one_smul] at hb
  change (∑ m ∈ range M, ‖fourierCoeffOn zero_lt_one f (m:ℤ)‖^2) ≤ _ at hb
  simpa only [hco] using hb

private theorem coeff_error {F V : ℝ → ℂ} {A : ℝ} (M : ℕ)
    (hF : MemLp F 2 μ01) (hV : MemLp V 2 μ01)
    (herr : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖F t - V t‖ ≤ A) :
    ∑ m ∈ range M, ‖coeff (fun t => F t ^ 2) m - coeff (fun t => V t ^ 2) m‖^2 ≤
      A^2 * ∫ t in (0:ℝ)..1, ‖F t + V t‖^2 := by
  let D := fun t => (F t)^2 - (V t)^2
  have hsum : MemLp (fun t => F t + V t) 2 μ01 := hF.add hV
  have hnorm : ∀ᵐ t ∂μ01, ‖D t‖ ≤ A*‖F t + V t‖ := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    change ‖F t ^ 2 - V t ^ 2‖ ≤ _
    rw [sq_sub_sq, norm_mul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (herr t ⟨ht.1.le, ht.2⟩) (norm_nonneg (F t + V t))
  have hD : MemLp D 2 μ01 := hsum.of_le_mul
    ((hF.aestronglyMeasurable.pow 2).sub (hV.aestronglyMeasurable.pow 2)) hnorm
  have hint (W : ℝ → ℂ) (hW : MemLp W 2 μ01) (m : ℕ) :
      IntervalIntegrable (fun t => W t ^ 2 * phase (-(m:ℝ)*t)) volume 0 1 := by
    have hi : Integrable (fun t => W t ^ 2) μ01 := by
      simpa only [pow_two, Pi.mul_apply] using
        (memLp_one_iff_integrable.mp (hW.fun_mul hW : MemLp (fun t => W t * W t) 1 μ01))
    have hii : IntervalIntegrable (fun t => W t ^ 2) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hi
    exact hii.mul_continuousOn (phase_cont m).continuousOn
  have hdiff (m : ℕ) : coeff D m =
      coeff (fun t => F t ^ 2) m - coeff (fun t => V t ^ 2) m := by
    unfold coeff D
    simp only [sub_mul]
    exact intervalIntegral.integral_sub (hint F hF m) (hint V hV m)
  simp_rw [← hdiff]
  apply (bessel M hD).trans
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    ← integral_const_mul]
  apply integral_mono_ae (hD.norm.integrable_sq) (hsum.norm.integrable_sq.const_mul _)
  filter_upwards [hnorm] with t ht
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) ht 2

end
end GoldbachSqrt

-- Fourier orthogonality adapted from TranswarpDrive, goldbach-proofs PR #158 (Apache-2.0).
namespace GoldbachSqrt.PairCoefficient
open MeasureTheory
private noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

theorem coefficient_pairs (w : ℕ → ℝ) (n Y : ℕ) :
    (∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range (Y+1), (w k : ℂ)*E ((k : ℝ)*t))^2 * E (-(n:ℝ)*t)) =
      ((∑ k ∈ Finset.range (Y+1), ∑ j ∈ Finset.range (Y+1),
        if k+j=n then w k*w j else 0 : ℝ) : ℂ) := by
  let I := Finset.range (Y+1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k : ℂ) * (w j : ℂ)) * E (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term, E]; fun_prop
  have hpoint (t : ℝ) : (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t) =
      ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t = ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  change (∫ t in (0:ℝ)..1, (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t))^2 * E (-(n:ℝ)*t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  simp only [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
  by_cases hj : k+j=n
  · have hz : (k:ℤ)+j-n=0 := by omega
    simp [hj,hz]
  · have hz : (k:ℤ)+j-n≠0 := by omega
    simp [hj,hz]


end GoldbachSqrt.PairCoefficient

-- The geometric-series count across half-intervals is adapted from
-- L_goldbach_grh_goldbach_exception_density.lean, namespace GoldbachDensityTransfer (Apache-2.0).
namespace GoldbachSqrt
noncomputable section
open Finset Filter GoldbachMajorArc MeasureTheory
open scoped Topology
def exceptional (n : ℕ) : Prop :=
  4 ≤ n ∧ Even n ∧ ((range (n+1)).filter (fun p => p.Prime ∧ (n-p).Prime)).card = 0

instance (n : ℕ) : Decidable (exceptional n) := by unfold exceptional; infer_instance
def exceptionSet (X : ℕ) := (range (X+1)).filter exceptional

theorem fresh_exceptions_bound {X : ℕ} {α A c : ℝ} {D : ℕ → ℝ}
    (hX : 0 < X) (hc : 0 < c)
    (hgap : ∀ n ∈ exceptionSet X \ exceptionSet (X/2), c * X ≤ D n)
    (hmean : ∑ n ∈ range (X+1), (D n)^2 ≤ A*(X:ℝ)^(2+α)) :
    ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) ≤ (A/c^2)*(X:ℝ)^α := by
  let S := exceptionSet X \ exceptionSet (X/2)
  have hXs : 0 < (X:ℝ) := by exact_mod_cast hX
  have hsub : S ⊆ range (X+1) := fun n hn => (mem_filter.mp (mem_sdiff.mp hn).1).1
  have ht : (S.card : ℝ)*(c*X)^2 ≤ ∑ n ∈ range (X+1), (D n)^2 := calc
    _ = ∑ _n ∈ S, (c*X)^2 := by simp
    _ ≤ ∑ n ∈ S, (D n)^2 :=
      sum_le_sum fun n hn => pow_le_pow_left₀ (by positivity) (hgap n hn) _
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => sq_nonneg _
  have hh := ht.trans hmean
  rw [Real.rpow_add hXs,Real.rpow_two] at hh
  change (S.card:ℝ) ≤ _
  rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos hc)]
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hXs)
  calc
    _ = (S.card:ℝ)*(c*X)^2 := by ring
    _ ≤ _ := hh
    _ = _ := by ring

/-- A power estimate on fresh exceptions in each half-interval gives the same
power for the cumulative count, including the finitely many small inputs. -/
theorem exceptionalCount_of_half_intervals {α K : ℝ} (hα : 0 < α) (N : ℕ)
    (fresh : ∀ X : ℕ, N ≤ X → ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) ≤ K*(X:ℝ)^α) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → ((exceptionSet X).card : ℝ) ≤ C*(X:ℝ)^α := by
  let B := max 2 N
  let q : ℝ := (1/2:ℝ)^α
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  let C := max (B+1:ℝ) (K/(1-q))
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < (B+1:ℝ)) (le_max_left ..)
  have hbudget : C*q+K ≤ C := by
    have hb := (div_le_iff₀ (sub_pos.mpr hq)).mp (show K/(1-q) ≤ C from le_max_right ..)
    linarith
  refine ⟨C,hC,fun X => ?_⟩
  induction X using Nat.strong_induction_on with
  | ind X ih =>
    intro hX
    have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
    have hXp := Real.one_le_rpow hXr hα.le
    by_cases hB : B ≤ X
    · have hB' : max 2 N ≤ X := hB
      have hhalf : 1 ≤ X/2 := by omega
      have hsmall := ih (X/2) (Nat.div_lt_self (by omega) (by norm_num)) hhalf
      have hratio : ((X/2 : ℕ):ℝ)^α ≤ q*(X:ℝ)^α := by
        dsimp [q]; rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤1/2) (Nat.cast_nonneg X)]
        apply Real.rpow_le_rpow (by positivity) _ hα.le
        have hh : X/2*2 ≤ X := Nat.div_mul_le_self ..
        have hh' : ((X/2:ℕ):ℝ)*2 ≤ X := by exact_mod_cast hh
        linarith
      have hfresh := fresh X (by omega)
      have hsub : exceptionSet (X/2) ⊆ exceptionSet X := by
        intro n hn
        obtain ⟨hr,he⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hr; omega),he⟩
      have hcard := card_sdiff_add_card_eq_card hsub
      have hh : ((exceptionSet X).card : ℝ) =
          ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) + ((exceptionSet (X/2)).card : ℝ) := by
        exact_mod_cast hcard.symm
      calc
        _ = _ := hh
        _ ≤ K*(X:ℝ)^α+C*(q*(X:ℝ)^α) := add_le_add hfresh (hsmall.trans (mul_le_mul_of_nonneg_left hratio hC.le))
        _ = (C*q+K)*(X:ℝ)^α := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hcard := card_le_card (filter_subset exceptional (range (X+1)))
      simp only [card_range] at hcard
      calc
        _ ≤ ((X+1:ℕ):ℝ) := by exact_mod_cast hcard
        _ ≤ (B+1:ℝ) := by push_cast; exact_mod_cast (by omega : X+1 ≤ B+1)
        _ ≤ C := le_max_left ..
        _ ≤ _ := le_mul_of_one_le_right hC.le hXp

theorem near_info {n X : ℕ} (h : n ∈ exceptionSet X \ exceptionSet (X/2)) :
    X/2 < n ∧ n ≤ X ∧ exceptional n := by
  obtain ⟨hmem,hnout⟩ := mem_sdiff.mp h
  obtain ⟨hr,he⟩ := mem_filter.mp hmem
  refine ⟨?_,Nat.le_of_lt_succ (mem_range.mp hr),he⟩
  by_contra! hlt
  exact hnout (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hlt),he⟩)


end
end GoldbachSqrt

namespace GoldbachSqrt
noncomputable section
open Finset Filter MeasureTheory GoldbachMajorArc
open scoped Topology

private theorem prime_coeff_zero {n m : ℕ} (hm : exceptional m) :
    coeff (fun t => primeSum n t ^ 2) m = 0 := by
  have hnoreps : ((range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)) = ∅ :=
    card_eq_zero.mp hm.2.2
  have hw (k j : ℕ) (h : k+j=m) : primeWeight k * primeWeight j = 0 := by
    by_cases hk : k.Prime
    · have hj : ¬j.Prime := by
        intro hj
        have hmem : k ∈ (range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime) :=
          mem_filter.mpr ⟨mem_range.mpr (by omega), hk, by simpa only [show m-k=j by omega] using hj⟩
        simpa [hnoreps] using hmem
      simp [primeWeight,hj]
    · simp [primeWeight,hk]
  have hz : (∑ k ∈ range (n+1), ∑ j ∈ range (n+1),
      if k+j=m then primeWeight k * primeWeight j else 0 : ℝ) = 0 := by
    apply sum_eq_zero
    intro k _
    apply sum_eq_zero
    intro j _
    split_ifs with h
    · exact hw k j h
    · rfl
  calc
    _ = ((∑ k ∈ range (n+1), ∑ j ∈ range (n+1),
          if k+j=m then primeWeight k * primeWeight j else 0 : ℝ):ℂ) :=
      PairCoefficient.coefficient_pairs primeWeight m n
    _ = 0 := by rw [hz]; norm_num

theorem count_from_uniform_model
    (ha : ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Set.Icc (0:ℝ) 1, ‖primeSum n t - model n t‖ ≤ C*(n:ℝ)^(3/4:ℝ)*(L n)^k) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      ((exceptionSet X).card:ℝ) ≤ (X:ℝ)^(1/2+ε) := by
  obtain ⟨C,k,hC,ha⟩ := ha
  intro ε he
  have hα : 0 < (1/2:ℝ)+ε/2 := by positivity
  have hgeo : ∀ᶠ n : ℕ in atTop, 2*H n*Q n<n ∧ Q n≤n := by
    filter_upwards [eventually_geometry] with n hn
    refine ⟨hn.2.2.2.1, ?_⟩
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from hn.1)
    apply Nat.cast_le.mp (α:=ℝ)
    calc
      (Q n:ℝ) ≤ ((n:ℝ)^(1/6:ℝ))^2 := Nat.floor_le (sq_nonneg _)
      _ = (n:ℝ)^(1/3:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
      _ ≤ _ := by simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3:ℝ)≤1)
  obtain ⟨B,hB,henergy⟩ := energy_of_geometry hgeo (ε/4) (by positivity)
  let A : ℝ := C^2*B
  let c : ℝ := 1/8
  have hc : 0 < c := by norm_num [c]
  have hfresh : ∀ᶠ X : ℕ in atTop,
      ((exceptionSet X \ exceptionSet (X/2)).card:ℝ) ≤ (A/c^2)*(X:ℝ)^(1/2+ε/2) := by
    filter_upwards [ha,henergy,eventually_geometry,
      eventually_L_pow k (by positivity : (0:ℝ)<ε/8)] with X hU hE hg hLpow
    obtain ⟨hX,hQ,hL,hsep,hlog,hwidth⟩ := hg
    have hp : 0 < (X:ℝ) := by exact_mod_cast hX
    let u : ℝ := 3/4+ε/8
    have hsup (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
        ‖primeSum X t-model X t‖ ≤ C*(X:ℝ)^u := by
      calc
        _ ≤ _ := hU t ht
        _ ≤ C*(X:ℝ)^(3/4:ℝ)*(X:ℝ)^(ε/8) := mul_le_mul_of_nonneg_left hLpow (by positivity)
        _ = _ := by dsimp [u]; rw [Real.rpow_add hp]; ring
    have hF : Continuous (primeSum X) := by unfold primeSum phase; fun_prop
    let D := fun m => ‖coeff (fun t => primeSum X t ^ 2) m - coeff (fun t => model X t ^ 2) m‖
    have hs : ∑ m ∈ range (X+1), (D m)^2 ≤ A*(X:ℝ)^(2+(1/2+ε/2)) := by
      calc
        _ ≤ (C*(X:ℝ)^u)^2 * ∫ t in (0:ℝ)..1, ‖primeSum X t + model X t‖^2 :=
          coeff_error (X+1) (continuous_memLp hF) (model_memLp_two X) hsup
        _ ≤ (C*(X:ℝ)^u)^2 * (B*(X:ℝ)^(1+ε/4)) :=
          mul_le_mul_of_nonneg_left hE (sq_nonneg _)
        _ = A * ((X:ℝ)^u * (X:ℝ)^u * (X:ℝ)^(1+ε/4)) := by dsimp [A]; ring
        _ = _ := by rw [← Real.rpow_add hp, ← Real.rpow_add hp]; dsimp [u]; congr 2; ring
    apply fresh_exceptions_bound hX hc (D:=D) _ hs
    intro m hm
    obtain ⟨hmlo,hmhi,hbad⟩ := near_info hm
    have hfloor := ideal_floor hX hQ hL hlog
      (fun q hq => hwidth q (mem_Icc.mp hq).1) hmlo hmhi hbad.2.1
    have hcoeff : (X:ℝ)/8 ≤ (coeff (fun t => model X t ^ 2) m).re := by
      rw [model_coefficient m hsep hQ]
      exact hfloor
    dsimp only [D]
    rw [prime_coeff_zero hbad, zero_sub, norm_neg]
    calc
      c * (X:ℝ) = (X:ℝ)/8 := by dsimp [c]; ring
      _ ≤ _ := hcoeff.trans (Complex.re_le_norm _)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hfresh
  obtain ⟨K,hK,hcount⟩ := exceptionalCount_of_half_intervals hα N hN
  have ht := (tendsto_rpow_atTop (by positivity : (0:ℝ)<ε/2)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (1:ℕ), ht.eventually_ge_atTop K] with X hX hpow
  have hp : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  calc
    _ ≤ K*(X:ℝ)^(1/2+ε/2) := hcount X hX
    _ ≤ (X:ℝ)^(ε/2)*(X:ℝ)^(1/2+ε/2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp.le _)
    _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring

end
end GoldbachSqrt

theorem Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions :
    let e := fun u : ℝ => Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I); let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let S := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * e ((k : ℝ) * t); let L := fun n : ℕ => (Nat.log 2 (n + 2) : ℝ); let Q := fun n : ℕ => ⌊((n : ℝ) ^ (1 / 6 : ℝ)) ^ 2⌋₊; let H : ℕ → ℕ := fun n => 256 * Q n * (Nat.log 2 (n + 2)) ^ 2; let center := fun q a : ℕ => (a : ℝ) / q; let width := fun n q : ℕ => (H n : ℝ) / ((q : ℝ) * n); let mean := fun q a : ℕ => (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), e ((r : ℝ) * center q a)) / (q.totient : ℂ); let K := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n + 1), e ((k : ℝ) * t); let model := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q), (Set.Icc (center q a - width n q) (center q a + width n q)).indicator (fun u => mean q a * K n (u - center q a)) t; (∃ (C : ℝ) (k : ℕ), 0 < C ∧ Filter.Eventually (fun n : ℕ => ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖S n t - model n t‖ ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) * L n ^ k) Filter.atTop) → ∀ ε : ℝ, 0 < ε → let reps := fun n : ℕ => (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p)); ∃ N : ℕ, ∀ X : ℕ, N ≤ X → (((Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0)).card : ℝ) ≤ (X : ℝ) ^ (1 / 2 + ε) :=
  GoldbachSqrt.count_from_uniform_model
