import Mathlib
import Conjectures.Goldbach.EstermannAlmostAllPolylog

/-! A uniform reflected Fourier coefficient on the polylogarithmic major arcs. -/

open Finset MeasureTheory Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

/- The clipped-interval and denominator decomposition below is adapted from
Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachBlockGeometry.
Here D is the maximum retained denominator and Q is the numerator in every arc width. -/
namespace ReflectedCoreGeometry
noncomputable section
open Finset Filter MeasureTheory

def width (Q n q : ℕ) : ℝ := (Q:ℝ)/((q:ℝ)*n)
def arcs (D Q n : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ a.Coprime q ∧
  |t-(a:ℝ)/q| ≤ width Q n q}
def numerators (q : ℕ) := (range (q+1)).filter (fun a => a.Coprime q)
def center (q a : ℕ) : ℝ := (a : ℝ) / q
def window (Q n q a : ℕ) : Set ℝ := Set.Icc (center q a - width Q n q) (center q a + width Q n q)
def leftEnd (Q n q a : ℕ) : ℝ := max (center q a - width Q n q) 0 - center q a
def rightEnd (Q n q a : ℕ) : ℝ := min (center q a + width Q n q) 1 - center q a


variable {D Q : ℕ}

theorem width_nonneg (n q : ℕ) : 0 ≤ width Q n q := by unfold width; positivity

theorem mem_window (n q a : ℕ) (t : ℝ) : t ∈ window Q n q a ↔ |t - center q a| ≤ width Q n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap {n q r a b : ℕ} {t : ℝ} (hn : 2 * Q^2 < n)
    (hq : q ∈ Icc 1 Q) (hr : r ∈ Icc 1 Q)
    (ha : t ∈ window Q n q a) (hb : t ∈ window Q n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : Q * r + Q * q < n := by nlinarith only [hn, Nat.mul_le_mul_left Q hrQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : (Q : ℝ) / (q*n) + Q/(r*n) < 1/(q*r) := calc
    _ = ((Q : ℝ)*r+Q*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  by_contra hne
  have hsep : 1 / ((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
    rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a:ℝ)*r - b*q)]
    · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a:ℝ)*r - b*q)]
  have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
  rw [abs_sub_comm ((a:ℝ)/q) t] at ht
  have h₁ := (mem_window (Q := Q) n q a t).mp ha
  have h₂ := (mem_window (Q := Q) n r b t).mp hb
  change |t-(a:ℝ)/q| ≤ (Q:ℝ)/(q*n) at h₁
  change |t-(b:ℝ)/r| ≤ (Q:ℝ)/(r*n) at h₂
  linarith

private theorem center_unique {n q r a b : ℕ} {t : ℝ} (hn : 2*Q^2<n)
    (hq : q ∈ Icc 1 Q) (hr : r ∈ Icc 1 Q)
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window Q n q a) (htb : t ∈ window Q n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

theorem arc_indicator_sum (F : ℝ → ℂ) {n : ℕ} (hDQ : D ≤ Q) (hn : 2*Q^2<n) (t : ℝ) :
    (arcs D Q n).indicator F t =
    ∑ q ∈ Icc 1 D, ∑ a ∈ numerators q, (window Q n q a).indicator F t := by
  classical
  have liftD {k : ℕ} (hk : k ∈ Icc 1 D) : k ∈ Icc 1 Q :=
    mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hDQ⟩
  by_cases ht : t ∈ arcs D Q n
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    have hw := (mem_window (Q := Q) n q a t).mpr habs
    symm
    calc
      _ = ∑ b ∈ numerators q, (window Q n q b).indicator F t := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => hrq (center_unique hn (liftD hr) (liftD hq) hb ha' ht' hw).1) _
      _ = (window Q n q a).indicator F t := by
        exact sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem (fun ht' => hba (center_unique hn (liftD hq) (liftD hq) hb ha' ht' hw).2) _
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw => ht ⟨q,a,(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1),(mem_filter.mp ha).2,(mem_window (Q := Q) n q a t).mp hw⟩) _

theorem center_in_unit {q a : ℕ} (hq : 0<q) (ha : a≤q) :
    0 ≤ center q a ∧ center q a ≤ 1 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  exact ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩

theorem clipped_order {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    -width Q n q ≤ leftEnd Q n q a ∧ leftEnd Q n q a ≤ rightEnd Q n q a ∧ rightEnd Q n q a ≤ width Q n q := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg (Q := Q) n q
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a-width Q n q) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a+width Q n q) 1]

theorem indicator_clipped {n q a : ℕ} (hq : 0<q) (ha : a≤q) (F : ℝ→ℂ) :
    (∫ t in (0:ℝ)..1, (window Q n q a).indicator F t) =
    ∫ β in leftEnd Q n q a..rightEnd Q n q a, F (center q a+β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order (Q := Q) (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    window, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : max (center q a-width Q n q) 0 ≤ min (center q a+width Q n q) 1),
    ← integral_Icc_eq_integral_Ioc]

def majorContribution (D Q n : ℕ) (F : ℝ → ℂ) : ℂ := ∫ t in (0:ℝ)..1, (arcs D Q n).indicator F t
def actualPiece (Q n q a : ℕ) (F : ℝ → ℂ) : ℂ := ∫ β in leftEnd Q n q a..rightEnd Q n q a, F (center q a+β)

theorem major_split (F : ℝ → ℂ) (hcont : Continuous F) {n : ℕ} (hDQ : D ≤ Q) (hn : 2*Q^2<n) : majorContribution D Q n F =
    ∑ q ∈ Icc 1 D, ∑ a ∈ numerators q, actualPiece Q n q a F := by
  have hInt (q a : ℕ) : IntervalIntegrable ((window Q n q a).indicator F) volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  unfold majorContribution
  simp_rw [arc_indicator_sum F hDQ hn]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ => hInt q a)]
    exact sum_congr rfl fun a ha => indicator_clipped (mem_Icc.mp hq).1
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)) _
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ => (hInt q a).1),
      integrable_finsetSum _ (fun a _ => (hInt q a).2)⟩


theorem width_le_unit {n q : ℕ} (hn : 2*Q^2<n) (hq : 0<q) :
    width Q n q ≤ 1/(q:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hQn : Q ≤ n := by nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) Q]
  calc
    width Q n q = ((Q:ℝ)/n)/q := by unfold width; ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hQn)) hq'.le

private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut {n q a : ℕ} (hn : 2*Q^2<n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd Q n q a = -(width Q n q) ∧ rightEnd Q n q a = width Q n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring


def modelPiece (Q n q a : ℕ) (C : ℕ → ℕ → ℂ) (K : ℝ → ℂ) : ℂ :=
  C q a * ∫ β in leftEnd Q n q a..rightEnd Q n q a, K β

private theorem endpoint_models (K : ℝ → ℂ) (hK : Continuous K) (C : ℕ → ℕ → ℂ) (hC : C 1 0 = C 1 1)
    {n : ℕ} (hn : 2*Q^2<n) :
    (∑ a ∈ numerators 1, modelPiece Q n 1 a C K) =
      C 1 0 * ∫ β in -(width Q n 1)..width Q n 1, K β := by
  let w := width Q n 1
  have hw : 0≤w := width_nonneg _ _
  have hw1 : w≤1 := by simpa [w] using width_le_unit hn (by decide : 0<1)
  have h0 : leftEnd Q n 1 0 = 0 ∧ rightEnd Q n 1 0 = w := by
    change max (0/(1:ℝ)-w) 0 - 0/1 = 0 ∧ min (0/1+w) 1 - 0/1 = w
    simp [hw,hw1]
  have h1 : leftEnd Q n 1 1 = -w ∧ rightEnd Q n 1 1 = 0 := by
    change max (1/(1:ℝ)-w) 0 - 1/1 = -w ∧ min (1/1+w) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (μ := volume) (-w) 0) (hK.intervalIntegrable 0 w)
  rw [show numerators 1 = {0,1} by decide]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}),sum_singleton,modelPiece,h0.1,h0.2,h1.1,h1.2]
  rw [← hC, ← mul_add, add_comm, hadd]

private theorem model_by_denominator (C : ℕ → ℕ → ℂ) (K : ℝ → ℂ)
    (hK : Continuous K) (hC : C 1 0 = C 1 1) {n q : ℕ} (hn : 2*Q^2<n) (hq : 0<q) :
    (∑ a ∈ numerators q, modelPiece Q n q a C K) =
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) *
      ∫ β in -(width Q n q)..width Q n q, K β := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h | h
  · subst q
    have hone : (range 1).filter (fun a => a.Coprime 1) = {0} := by decide
    rw [hone,sum_singleton]
    exact endpoint_models K hK C hC hn
  · have hs : numerators q = (range q).filter (fun a => a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (interior_order h ha).2, (mem_filter.mp ha).2⟩
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ha).1; omega),(mem_filter.mp ha).2⟩
    rw [← hs, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨hl,hr⟩ := uncut hn h ha
    simp only [modelPiece,hl,hr]

theorem major_error (F K : ℝ → ℂ) (hF : Continuous F) (hK : Continuous K)
    (C : ℕ → ℕ → ℂ) (hC : C 1 0 = C 1 1) {n : ℕ} (hDQ : D ≤ Q) (hn : 2*Q^2<n) :
    ‖majorContribution D Q n F - ∑ q ∈ Icc 1 D,
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) *
      ∫ β in -(width Q n q)..width Q n q, K β‖ ≤
    ∑ q ∈ Icc 1 D, ∑ a ∈ range (q+1), ∫ β in -(width Q n q)..width Q n q,
      ‖F (center q a+β) - C q a*K β‖ := by
  rw [major_split F hF hDQ hn]
  have hmodel (q : ℕ) (hq : q ∈ Icc 1 D) := model_by_denominator C K hK hC hn (mem_Icc.mp hq).1
  rw [← sum_congr rfl hmodel, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun q hq => ?_)
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun a ha => ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ =>
      intervalIntegral.integral_nonneg (by linarith [width_nonneg (Q := Q) n q]) fun _ _ => norm_nonneg _)))
  have hi : Continuous (fun β => F (center q a+β)) := hF.comp (continuous_const.add continuous_id)
  have hm : Continuous (fun β => C q a*K β) := continuous_const.mul hK
  have ⟨hl,ho,hr⟩ := clipped_order (Q := Q) (n := n) (mem_Icc.mp hq).1
    (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1))
  rw [actualPiece,modelPiece,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub
    (hi.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
  exact (intervalIntegral.norm_integral_le_integral_norm ho).trans
    (intervalIntegral.integral_mono_interval hl ho hr (Eventually.of_forall fun _ => norm_nonneg _)
      ((hi.sub hm).norm.intervalIntegrable _ _))

end
end ReflectedCoreGeometry

namespace ReflectedCoreApprox
open Finset Filter MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
open scoped Topology
noncomputable section

theorem ram_at_one (q:ℕ):ram q 1=(ArithmeticFunction.moebius q:ℂ):=by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [ram]
  | one => simp [ram_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ j =>
      have no (l:ℕ):¬p^(l+1)∣1:=
        fun dv=>hp.not_dvd_one ((dvd_pow_self p (Nat.succ_ne_zero l)).trans dv)
      rw [ram_primePower p j 1 hp,ite_eq_right (no j),ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero j)]
      cases j with
      | zero => simp
      | succ l => simp [no l]
  | coprime a b ha hb ab ia ib =>
    rw [ram_mul (by omega) (by omega) ab,ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime ab,Int.cast_mul,ia,ib]

theorem core_point_estimate {X q a:ℕ} (xp:0<X) (qp:0<q) (cop:a.Coprime q) {β:ℝ}
    (near:|β|≤(Polylog.cutoff 3 X:ℝ)/((q:ℝ)*X)):
    ‖primeSum X ((a:ℝ)/q+β)-((ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ))*kernel X β‖≤
      prefixError X ((a:ℝ)/q) (unitMean q a)*(1+2*Real.pi*((Polylog.cutoff 3 X:ℝ)/q)):=by
  have h:=Polylog.rational_arc_error (a:=a) xp qp near
  rwa [show ((ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ))=unitMean q a by rw [unitMean_eq_ram cop,ram_at_one]]

theorem core_model_point (X q a m:ℕ) (β:ℝ):
    ‖primeSum X ((a:ℝ)/q+β)^2*phase (-(m:ℝ)*((a:ℝ)/q+β))-
      ((unitMean q a)^2*phase (-(m:ℝ)*((a:ℝ)/q)))*(kernel X β^2*phase (-(m:ℝ)*β))‖=
    Polylog.modelError X q a m β:=by
  have add (y z:ℝ):phase (y+z)=phase y*phase z:=by
    unfold phase;rw [←Complex.exp_add];congr 1;push_cast;ring
  have eq:((unitMean q a)^2*phase (-(m:ℝ)*((a:ℝ)/q)))*(kernel X β^2*phase (-(m:ℝ)*β))=
      (unitMean q a*kernel X β)^2*phase (-(m:ℝ)*((a:ℝ)/q+β)):=by
    rw [mul_add,add];ring
  rw [eq];rfl

theorem center_endpoints (m:ℕ):
    (unitMean 1 0)^2*phase (-(m:ℝ)*((0:ℝ)/1))=
      (unitMean 1 1)^2*phase (-(m:ℝ)*((1:ℝ)/1)):=by
  have um (a:ℕ):unitMean 1 a=1:=by rw [unitMean_eq_ram (by simp),ram_one];simp
  have ph:phase (-(m:ℝ))=1:=by
    unfold phase
    have eq:(((2*Real.pi* -(m:ℝ):ℝ):ℂ)*Complex.I)=(-(m:ℂ))*(2*(Real.pi:ℂ)*Complex.I):=by push_cast;ring
    rw [eq,←Int.cast_natCast (R:=ℂ) m,←Int.cast_neg,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow]
  simp only [um,one_pow,zero_div,mul_zero,one_div_one,mul_one,one_mul,ph]
  simp [phase]

theorem prime_sum_filter (X:ℕ) (t:ℝ):
    primeSum X t=∑p∈(range (X+1)).filter Nat.Prime,(Real.log p:ℂ)*phase ((p:ℝ)*t):=by
  unfold primeSum;rw [sum_filter];apply sum_congr rfl;intro p _
  by_cases hp:p.Prime <;>simp [primeWeight,hp]

theorem core_error_small (ε:ℝ) (he:0<ε):
    ∀ᶠ X:ℕ in atTop,∀m:ℕ,
    (∑q∈Icc 1 (Nat.log 2 (X+2)),∑a∈range (q+1),
      ∫β in -(Polylog.width (Polylog.cutoff 3 X) X q)..(Polylog.width (Polylog.cutoff 3 X) X q),
       ‖primeSum X ((a:ℝ)/q+β)^2*phase (-(m:ℝ)*((a:ℝ)/q+β))-
        ((unitMean q a)^2*phase (-(m:ℝ)*((a:ℝ)/q)))*(kernel X β^2*phase (-(m:ℝ)*β))‖)≤ε*X:=by
  filter_upwards [Polylog.eventually_totalArcError_lt 3 0 (by decide) he] with X bound
  intro m
  simp_rw [core_model_point]
  have le:Nat.log 2 (X+2)≤Polylog.cutoff 3 X:=Nat.le_self_pow (by decide : 3≠0) _
  apply le_trans _ (show Polylog.totalArcError (Polylog.cutoff 3 X) X m≤ε*X by simpa only [pow_zero,one_mul] using (bound (m:ℝ)).le)
  unfold Polylog.totalArcError
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl le)
  intro q _ _
  apply sum_nonneg;intro a _
  have width:0≤Polylog.width (Polylog.cutoff 3 X) X q:=by unfold Polylog.width;positivity
  exact intervalIntegral.integral_nonneg (by linarith only [width]) (fun _ _=>norm_nonneg _)

end
end ReflectedCoreApprox

namespace ReflectedCoreKernel
open Finset MeasureTheory Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
noncomputable section

def model (X m : ℕ) (t : ℝ) : ℂ := kernel X t ^ 2 * phase (-(m:ℝ)*t)

theorem continuous_model (X m : ℕ) : Continuous (model X m) := by
  unfold model kernel phase
  fun_prop

private lemma add_phase (x y : ℝ) : phase (x+y)=phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem mode (j : ℤ) :
    (∫ t in (-(1/2) : ℝ)..1/2, phase ((j : ℝ) * t)) = if j = 0 then 1 else 0 := by
  have hi : phase (j:ℝ) = 1 := by
    unfold phase
    convert Complex.exp_int_mul_two_pi_mul_I j using 2
    push_cast
    ring
  have hp : Function.Periodic (fun t : ℝ => phase ((j : ℝ) * t)) 1 := by
    intro t
    simp only [mul_add, mul_one, add_phase, hi, mul_one]
  have hs := hp.intervalIntegral_add_eq (-(1/2)) 0
  norm_num only [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num, zero_add] at hs
  rw [hs]
  by_cases hj : j = 0
  · subst j; simp [phase]
  let c : ℂ := (j : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((j : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c; congr 1; push_cast; ring
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hj)
    (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hj, c, Complex.exp_int_mul_two_pi_mul_I]

theorem full {X m : ℕ} (hXm : X ≤ m) (hmX : m ≤ 2*X) :
    (∫ t in (-(1/2) : ℝ)..1/2, model X m t) = (2*X+1-m : ℂ) := by
  let I := range (X+1)
  let f (k j : ℕ) (t : ℝ) := phase (((k : ℤ) + (j : ℤ) - m : ℤ) * (t : ℝ))
  have cf (k j : ℕ) : Continuous (f k j) := by dsimp [f, phase]; fun_prop
  have expanded (t : ℝ) : model X m t = ∑ k ∈ I, ∑ j ∈ I, f k j t := by
    dsimp [model, kernel, I]
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
    dsimp [f]; push_cast; rw [← add_phase, ← add_phase]; congr 1; ring
  have row (k : ℕ) (hk : k ∈ I) :
      (∫ t in (-(1/2) : ℝ)..1/2, ∑ j ∈ I, f k j t) = if m-X ≤ k then 1 else 0 := by
    have kX : k ≤ X := by simpa [I, Nat.lt_succ_iff] using hk
    rw [intervalIntegral.integral_finsetSum (fun j _ => (cf k j).intervalIntegrable _ _)]
    simp only [f, mode]
    by_cases good : m-X ≤ k
    · rw [ite_eq_left good, sum_eq_single_of_mem (m-k) (show m-k ∈ I by apply mem_range.mpr; omega)]
      · simp [show (k : ℤ) + ↑(m-k) - ↑m = 0 by omega]
      · intro j _ hj; simp [show (k : ℤ) + ↑j - ↑m ≠ 0 by omega]
    · rw [ite_eq_right good]; apply sum_eq_zero; intro j hj
      have jX : j ≤ X := by simpa [I, Nat.lt_succ_iff] using hj
      simp [show (k : ℤ) + ↑j - ↑m ≠ 0 by omega]
  simp_rw [expanded]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (continuous_finsetSum I fun j _ => cf k j).intervalIntegrable _ _)]
  trans ∑ k ∈ I, if m-X ≤ k then (1:ℂ) else 0
  · exact sum_congr rfl row
  rw [← Finset.sum_filter]
  have hf : I.filter (fun k => m-X≤k) = Finset.Icc (m-X) X := by
    ext k; simp only [I, mem_filter, mem_range, mem_Icc]; omega
  rw [hf]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
  have count : X+1-(m-X) + m = 2*X+1 := by omega
  have cc : ((X+1-(m-X) : ℕ):ℂ) +m=2*X+1 := by exact_mod_cast count
  linear_combination cc

private theorem kernel_inv (X m : ℕ) {x : ℝ} (xp : 0 < |x|) (xh : |x| ≤ 1/2) :
    ‖model X m x‖ ≤ x^(-2:ℤ) := by
  have sinLower := OAI.Problem337.sin_pi_mul_lower_on_middle (δ := |x|) (x := |x|)
    xp le_rfl (by linarith)
  have positive : 0 < Real.sin (Real.pi * |x|) := by linarith
  have sa : |Real.sin (Real.pi*x)| = Real.sin (Real.pi*|x|) := by
    by_cases xn : 0 ≤ x
    · simpa [abs_of_nonneg xn] using (abs_of_pos positive)
    · rw [abs_of_neg (lt_of_not_ge xn), mul_neg, Real.sin_neg] at positive ⊢
      rw [abs_of_neg (by linarith)]
  have nonzero : Real.sin (Real.pi*x) ≠ 0 := abs_pos.mp (sa.symm ▸ positive)
  have h : ‖kernel X x‖ ≤ 1/(2*|x|) := calc
    _ = ‖∑ k ∈ range (X+1), Complex.exp (Complex.I*((2*Real.pi*x:ℝ):ℂ))^k‖ := by
      congr 1
      apply sum_congr rfl
      intro k _
      rw [← Complex.exp_nat_mul]
      unfold phase
      congr 1
      push_cast
      ring
    _ ≤ 1/|Real.sin (Real.pi*x)| := OAI.Problem337.norm_geometric_phase_sum_le nonzero _
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (sa.symm ▸ sinLower)
  have a : ‖kernel X x‖ ≤ |x|⁻¹ := h.trans (by
    rw [← one_div]
    exact one_div_le_one_div_of_le xp (by linarith))
  have b := pow_le_pow_left₀ (norm_nonneg _) a 2
  rw [model, norm_mul, norm_pow, show ‖phase (-(m:ℝ)*x)‖=1 from Complex.norm_exp_ofReal_mul_I _, mul_one]
  convert b using 1
  simp [zpow_neg, inv_pow, sq_abs]

private theorem wing {b : ℝ} (hb : 0 < b) (bh : b ≤ 1/2) (f : ℝ → ℂ)
    (hf : ∀ t ∈ Set.Ioc b (1/2:ℝ), ‖f t‖ ≤ t ^ (-2:ℤ)) :
    ‖∫ t in b..1/2, f t‖ ≤ 1/b := by
  have away : (0:ℝ) ∉ Set.uIcc b (1/2:ℝ) := by rw [Set.uIcc_of_le bh]; simp [hb.not_ge]
  have hi : IntervalIntegrable (fun t : ℝ => t^(-2:ℤ)) volume b (1/2) :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr away)
  apply (intervalIntegral.norm_integral_le_of_norm_le bh (Filter.Eventually.of_forall hf) hi).trans
  rw [integral_zpow (Or.inr ⟨by decide,away⟩)]
  norm_num [one_div]
  linarith

theorem tail {X m : ℕ} (hXm : X ≤ m) (hmX : m ≤ 2*X) {b : ℝ} (hb : 0 < b) (bh : b ≤ 1/2) :
    ‖(∫ t in -b..b, model X m t) - (2*X+1-m:ℂ)‖ ≤ 2/b := by
  have hn : ‖∫ t in -(1/2:ℝ)..-b, model X m t‖ ≤ 1/b := by
    rw [← intervalIntegral.integral_comp_neg (model X m)]
    apply wing hb bh
    intro t ht
    have pos := hb.trans ht.1
    simpa [abs_of_pos pos] using kernel_inv X m (x := -t) (by simpa [abs_of_pos pos] using pos)
      (by simpa [abs_of_pos pos] using ht.2)
  have hp : ‖∫ t in b..1/2, model X m t‖ ≤ 1/b := by
    apply wing hb bh
    intro t ht
    have pos := hb.trans ht.1
    exact kernel_inv X m (by simpa only [abs_of_pos pos] using pos) (by simpa only [abs_of_pos pos] using ht.2)
  have integ (a c : ℝ) : IntervalIntegrable (model X m) volume a c :=
    (continuous_model X m).intervalIntegrable _ _
  have total := (intervalIntegral.integral_add_adjacent_intervals (integ (-(1/2)) (-b)) (integ (-b) b))
  have total' := intervalIntegral.integral_add_adjacent_intervals (integ (-(1/2)) b) (integ b (1/2))
  rw [← total, full hXm hmX] at total'
  have eqn : (∫ t in -b..b, model X m t) - (2*X+1-m:ℂ) =
      -((∫ t in -(1/2:ℝ)..-b, model X m t)+(∫ t in b..1/2, model X m t)) := by
    linear_combination total'
  rw [eqn,norm_neg]
  exact (norm_add_le _ _).trans ((add_le_add hn hp).trans_eq (by ring))

end
end ReflectedCoreKernel

namespace ReflectedCoreArithmetic
open Finset GoldbachMajorArc
open scoped BigOperators

theorem coefficient_norm (q m : ℕ) (hq : 0 < q) : ‖coefficient q m‖ ≤ 1 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [coefficient_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => simp [coefficient_one]
    | succ k =>
      cases k with
      | zero =>
        simp only [zero_add,pow_one,coefficient_prime hp m, Complex.norm_real,Real.norm_eq_abs]
        have two : (2:ℝ)≤p := by exact_mod_cast hp.two_le
        have base : 0 < (p:ℝ)-1 := by linarith
        unfold localCoefficient
        split
        · rw [abs_of_nonneg (by positivity)]
          exact (div_le_one (by linarith)).mpr (by linarith)
        · rw [abs_neg,abs_of_nonneg (by positivity)]
          exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg ((p:ℝ)-2)])
      | succ k => simp [coefficient_higher_power hp]
  | coprime a b ha hb cp ia ib =>
    rw [coefficient_mul (by omega) (by omega) cp,norm_mul]
    simpa using mul_le_mul (ia (by omega)) (ib (by omega)) (norm_nonneg _) zero_le_one

theorem flat_floor (L m : ℕ) (lpos : 0 < L) (he : Even m) :
    (1/3:ℝ) ≤ ∑ q ∈ Icc 1 L, (coefficient q m).re := by
  let W (k : ℕ) : ℝ := if k≤L then 1 else 0
  have nonneg (k : ℕ) : 0≤W k := by unfold W;split <;> norm_num
  have mono (i j : ℕ) (_ : 0 < i) (hij : i≤j) : W j≤W i := by
    dsimp [W];split_ifs <;> norm_num <;> omega
  have floor:=arithmetic_floor (Q:=L) he W nonneg mono (by intro k hk; simp [W,not_le.mpr hk])
  rw [show W 1=1 by simp [W,lpos.ne']] at floor
  apply floor.trans_eq
  apply Finset.sum_congr rfl
  intro q hq
  simp [W,(Finset.mem_Icc.mp hq).2] 

theorem transferred {X L m : ℕ} (large : 128 ≤ L) (xp : 0 < X)
    (hm : 2*m ≤ 3*X) (he : Even m) (P : ℂ) (J : ℕ → ℂ)
    (approx : ‖P - ∑ q ∈ Icc 1 L, coefficient q m * J q‖ ≤ (X:ℝ)/64)
    (tail : ∀ q ∈ Icc 1 L, ‖J q - ((2*X+1-m:ℕ):ℂ)‖ ≤ 2 / ((L:ℝ)^3/((q:ℝ)*X))) :
    7*(X:ℝ)/64 ≤ P.re := by
  let t := 2*X+1-m
  have lp : 0 < L := by omega
  have lr : (128:ℝ)≤L := by exact_mod_cast large
  have ls : 0 < (L:ℝ) := by exact_mod_cast lp
  have xr : 0 < (X:ℝ) := by exact_mod_cast xp
  have half : (X:ℝ)≤2*(t:ℝ) := by exact_mod_cast (show X≤2*t by dsimp [t];omega)
  have step (q : ℕ) (hq : q∈Icc 1 L) : ‖J q - (t:ℂ)‖ ≤ (X:ℝ)/(64*L) := by
    apply (tail q hq).trans
    have qr : (q:ℝ) ≤ L := by exact_mod_cast (mem_Icc.mp hq).2
    rw [div_div_eq_mul_div,div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      _ ≤ 2*((L:ℝ)*X)*(64*L) := by gcongr
      _ = (X:ℝ)*((128:ℝ)*L^2) := by ring
      _ ≤ _ := by gcongr;calc (128:ℝ)*L^2 ≤ (L:ℝ)*L^2 := by gcongr
                              _ = _ := by ring
  let V := ∑ q ∈ Icc 1 L, coefficient q m * J q
  let U := ∑ q ∈ Icc 1 L, coefficient q m * (t:ℂ)
  have sub : ‖V-U‖ ≤ (X:ℝ)/64 := by
    dsimp only [V,U]
    rw [←sum_sub_distrib]
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _q ∈ Icc 1 L, (X:ℝ)/(64*L) := by
        apply sum_le_sum;intro q hq
        rw [←mul_sub,norm_mul]
        exact (mul_le_mul (coefficient_norm q m (mem_Icc.mp hq).1) (step q hq) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul];field_simp
  have floor := mul_le_mul_of_nonneg_right (flat_floor L m lp he) (Nat.cast_nonneg (α:=ℝ) t)
  have re : U.re=(∑ q ∈ Icc 1 L, (coefficient q m).re) * (t:ℝ) := by
    dsimp only [U];rw [←sum_mul,Complex.mul_re,Complex.re_sum];simp
  have first := (Complex.re_le_norm (V-P)).trans ((norm_sub_rev V P).le.trans approx)
  have second := (Complex.re_le_norm (U-V)).trans ((norm_sub_rev U V).le.trans sub)
  rw [Complex.sub_re] at first second
  linarith only [half,floor,re,first,second]

end ReflectedCoreArithmetic

namespace ReflectedCoreArithmetic
open Filter
theorem ranges : ∀ᶠ X : ℕ in atTop,
    128 ≤ Nat.log 2 (X+2) ∧ 2*((Nat.log 2 (X+2))^3)^2 < X := by
  have power (j : ℕ) : 2*(128+j)^6+3 ≤ 2^(128+j) := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      have step : 2*(128+j+1)^6+3 ≤ 2*(2*(128+j)^6+3) := by ring_nf;omega
      calc
        _ ≤ 2*(2*(128+j)^6+3) := step
        _ ≤ 2*2^(128+j) := Nat.mul_le_mul_left 2 ih
        _ = _ := by rw [Nat.add_succ,pow_succ,Nat.mul_comm]
  filter_upwards [eventually_ge_atTop (2^128 : ℕ)] with X hx
  have H : 128≤Nat.log 2 (X+2) := Nat.le_log_of_pow_le (by decide) (hx.trans (by omega))
  refine ⟨H,?_⟩
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le H
  have logpow := Nat.pow_log_le_self 2 (by omega : X+2≠0)
  have bound := power j
  rw [←hj] at bound
  rw [←pow_mul]
  norm_num at *
  omega
end ReflectedCoreArithmetic

namespace ReflectedCoreConclusion
open Finset Filter MeasureTheory GoldbachMajorArc
open ReflectedCoreGeometry
noncomputable section

set_option maxHeartbeats 1200000 in
theorem estimate : ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 2*m ≤ 3*X → 4*X ≤ 3*m → Even m →
    7*(X:ℝ)/64 ≤ (majorContribution (Nat.log 2 (X+2)) ((Nat.log 2 (X+2))^3) X
      (fun t => (primeSum X t)^2 * phase (-(m:ℝ)*t))).re := by
  filter_upwards [ReflectedCoreArithmetic.ranges,ReflectedCoreApprox.core_error_small (1/64) (by norm_num),eventually_ge_atTop (1:ℕ)] with X hX bound hx
  intro m hm lo he
  let L := Nat.log 2 (X+2)
  let H := L^3
  let C (q a : ℕ) := (unitMean q a)^2 * phase (-(m:ℝ)*((a:ℝ)/q))
  let F (t : ℝ) := (primeSum X t)^2 * phase (-(m:ℝ)*t)
  let K := ReflectedCoreKernel.model X m
  let J (q : ℕ) := ∫ t in -(ReflectedCoreGeometry.width H X q)..ReflectedCoreGeometry.width H X q, K t
  have LP : 128≤L := hX.1
  have pos : 0 < L := by omega
  have hp : 0<H := pow_pos pos _
  have sep : 2*H^2<X := hX.2
  have cont : Continuous F := by
    dsimp [F,primeSum,phase]
    fun_prop
  have ends : C 1 0 = C 1 1 := ReflectedCoreApprox.center_endpoints m
  have approx := ReflectedCoreGeometry.major_error F K cont (ReflectedCoreKernel.continuous_model X m) C ends
    (Nat.le_self_pow (by decide : 3≠0) L) sep
  have cerr (q : ℕ) : (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) = coefficient q m :=
    sum_centers_eq_coefficient q m
  simp_rw [cerr] at approx
  apply ReflectedCoreArithmetic.transferred LP hx hm he _ J
  · apply (approx.trans (bound m)).trans_eq
    ring
  · intro q hq
    have qp : 0 < q := (mem_Icc.mp hq).1
    have xr : 0 < (X:ℝ) := by exact_mod_cast hx
    have qr : 1 ≤ (q:ℝ) := by exact_mod_cast qp
    have hr : 0 < (H:ℝ) := by exact_mod_cast hp
    have rad : 0 < ReflectedCoreGeometry.width H X q := by unfold ReflectedCoreGeometry.width; positivity
    have hs : 2*H ≤ X := by nlinarith [Nat.le_self_pow (by decide : 2≠0) H]
    have half : ReflectedCoreGeometry.width H X q ≤ 1/2 := by
      unfold ReflectedCoreGeometry.width
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hsr : 2*(H:ℝ) ≤ X := by exact_mod_cast hs
      nlinarith only [hsr,mul_le_mul_of_nonneg_right qr xr.le]
    have tail := ReflectedCoreKernel.tail (show X ≤ m by omega) (show m ≤ 2*X by omega) rad half
    have left : m ≤ 2*X+1 := by omega
    simpa only [J,K,H,ReflectedCoreGeometry.width,Nat.cast_sub left,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat,Nat.cast_one,Nat.cast_pow] using tail

end
end ReflectedCoreConclusion

theorem Conjectures.Cuts.Taskba08eb3c3998330911d98843 : (have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range (x2 + (1 : ℕ)) with Nat.Prime x4, (↑(Real.log (↑x4 : ℝ)) : ℂ) * x1 ((↑x4 : ℝ) * x3); have x3 : ℕ → ℕ → ℝ → ℂ := fun (x3 x4 : ℕ) (x5 : ℝ) => x2 x3 x5 ^ (2 : ℕ) * x1 (-(↑x4 : ℝ) * x5); have x4 : ℕ → Set ℝ := fun (x4 : ℕ) =>   have x5 : ℕ := Nat.log (2 : ℕ) (x4 + (2 : ℕ));   {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x5 ^ (3 : ℕ)) : ℝ) / ((↑x7 : ℝ) * (↑x4 : ℝ))}; have x5 : Set ℝ → ℕ → ℕ → ℂ := fun (x5 : Set ℝ) (x6 x7 : ℕ) => intervalIntegral (x5.indicator (x3 x6 x7)) (0 : ℝ) (1 : ℝ) MeasureTheory.MeasureSpace.volume; ∃ (x6 : ℕ), ∀ x7 ≥ x6, ∀ (x9 : ℕ), (2 : ℕ) * x9 ≤ (3 : ℕ) * x7 → (4 : ℕ) * x7 ≤ (3 : ℕ) * x9 → Even x9 → (7 : ℝ) * (↑x7 : ℝ) / (64 : ℝ) ≤ (x5 (x4 x7) x7 x9).re) := by
  classical
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 ReflectedCoreConclusion.estimate
  refine ⟨N,?_⟩
  intro X hX m hi lo he
  have v := hN X hX m hi lo he
  change _ ≤ (∫ t in (0:ℝ)..1, (ReflectedCoreGeometry.arcs (Nat.log 2 (X+2)) ((Nat.log 2 (X+2))^3) X).indicator
    (fun t => (∑ p ∈ (Finset.range (X+1)).filter Nat.Prime,
      (Real.log p:ℂ) * GoldbachMajorArc.phase ((p:ℝ)*t)) ^ 2 * GoldbachMajorArc.phase (-(m:ℝ)*t)) t).re
  unfold ReflectedCoreGeometry.majorContribution at v
  simp_rw [ReflectedCoreApprox.prime_sum_filter] at v
  exact v
