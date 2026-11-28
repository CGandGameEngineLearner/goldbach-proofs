import Mathlib

section

open Finset
open scoped Classical BigOperators

namespace DigitalAdjacent

def W (b : ℕ) (D : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (b ^ k)).filter fun n =>
    (∀ i < k, n / b ^ i % b ∈ D) ∧
      ∀ i < k - 1, n / b ^ i % b ≠ n / b ^ (i + 1) % b

def Fiber (b : ℕ) (D : Finset ℕ) (k d : ℕ) : Finset ℕ :=
  (W b D (k + 1)).filter fun n => n / b ^ k = d

private theorem digit_append_low {b k i u d : ℕ} (hb : 0 < b) (hi : i ≤ k) :
    (u + d * b ^ (k + 1)) / b ^ i % b = u / b ^ i % b := by
  have hpow : b ^ (k + 1) = b ^ i * b ^ (k + 1 - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow' : b ^ (k + 1 - i) = b * b ^ (k - i) := by
    have hki : k + 1 - i = (k - i) + 1 := by omega
    rw [hki, pow_succ]
    ring
  rw [hpow, hpow']
  have heq : u + d * (b ^ i * (b * b ^ (k - i))) =
      u + b ^ i * (d * b ^ (k - i) * b) := by ring
  rw [heq, Nat.add_mul_div_left u (d * b ^ (k - i) * b) (pow_pos hb _)]
  simp [Nat.add_mod]

private theorem digit_append_top {b k u d : ℕ} (hb : 0 < b)
    (hu : u < b ^ (k + 1)) :
    (u + d * b ^ (k + 1)) / b ^ (k + 1) = d := by
  rw [Nat.add_mul_div_right u d (pow_pos hb _), Nat.div_eq_of_lt hu]
  simp

private theorem append_bound {b k u d : ℕ} (_hb : 0 < b)
    (hu : u < b ^ (k + 1)) (hd : d < b) :
    u + d * b ^ (k + 1) < b ^ (k + 2) := by
  calc
    u + d * b ^ (k + 1) < (d + 1) * b ^ (k + 1) := by nlinarith
    _ ≤ b * b ^ (k + 1) := by gcongr; omega
    _ = b ^ (k + 2) := by rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]; ring

theorem mem_W_append_iff {b k u d : ℕ} {D : Finset ℕ}
    (hb : 0 < b) (hd : d < b) (hu : u < b ^ (k + 1)) :
    u + d * b ^ (k + 1) ∈ W b D (k + 2) ↔
      u ∈ W b D (k + 1) ∧ d ∈ D ∧ u / b ^ k % b ≠ d := by
  simp only [W, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hdigits, hadj⟩
    have huW : u < b ^ (k + 1) ∧
        (∀ i < k + 1, u / b ^ i % b ∈ D) ∧
        ∀ i < k + 1 - 1, u / b ^ i % b ≠ u / b ^ (i + 1) % b := by
      refine ⟨hu, ?_, ?_⟩
      · intro i hi
        have hh := hdigits i (by omega : i < k + 2)
        rwa [digit_append_low hb (by omega : i ≤ k)] at hh
      · intro i hi
        have hh := hadj i (by omega : i < k + 2 - 1)
        rw [digit_append_low hb (by omega : i ≤ k),
          digit_append_low hb (by omega : i + 1 ≤ k)] at hh
        exact hh
    have htop := hdigits (k + 1) (by omega : k + 1 < k + 2)
    rw [digit_append_top hb hu, Nat.mod_eq_of_lt hd] at htop
    have hboundary := hadj k (by omega : k < k + 2 - 1)
    rw [digit_append_low hb (by omega : k ≤ k),
      digit_append_top hb hu, Nat.mod_eq_of_lt hd] at hboundary
    exact ⟨huW, htop, hboundary⟩
  · rintro ⟨⟨_, hdigits, hadj⟩, htop, hboundary⟩
    refine ⟨append_bound hb hu hd, ?_, ?_⟩
    · intro i hi
      by_cases hilow : i < k + 1
      · rw [digit_append_low hb (by omega : i ≤ k)]
        exact hdigits i hilow
      · have hieq : i = k + 1 := by omega
        subst i
        rwa [digit_append_top hb hu, Nat.mod_eq_of_lt hd]
    · intro i hi
      by_cases hilow : i < k
      · rw [digit_append_low hb (by omega : i ≤ k),
          digit_append_low hb (by omega : i + 1 ≤ k)]
        exact hadj i (by omega : i < k + 1 - 1)
      · have hieq : i = k := by omega
        subst i
        rwa [digit_append_low hb (by omega : k ≤ k),
          digit_append_top hb hu, Nat.mod_eq_of_lt hd]

private theorem top_quotient_lt {b k u : ℕ} (hb : 0 < b)
    (hu : u < b ^ (k + 1)) : u / b ^ k < b := by
  apply (Nat.div_lt_iff_lt_mul (pow_pos hb _)).mpr
  rw [mul_comm, ← pow_succ]
  exact hu

theorem mem_Fiber_append_iff {b k u d : ℕ} {D : Finset ℕ}
    (hb : 0 < b) (hd : d < b) (hu : u < b ^ (k + 1)) :
    u + d * b ^ (k + 1) ∈ Fiber b D (k + 1) d ↔
      u ∈ W b D (k + 1) ∧ d ∈ D ∧ u / b ^ k ≠ d := by
  simp only [Fiber, Finset.mem_filter]
  rw [digit_append_top hb hu]
  simp only [and_true]
  rw [mem_W_append_iff hb hd hu, Nat.mod_eq_of_lt (top_quotient_lt hb hu)]

theorem mem_Fiber_succ_iff {b k n d : ℕ} {D : Finset ℕ}
    (hb : 0 < b) (hd : d < b) (hdD : d ∈ D) :
    n ∈ Fiber b D (k + 1) d ↔
      ∃ c ∈ D.filter (· ≠ d), ∃ u ∈ Fiber b D k c,
        n = u + d * b ^ (k + 1) := by
  classical
  constructor
  · intro hn
    let u := n % b ^ (k + 1)
    let c := u / b ^ k
    have hu : u < b ^ (k + 1) := Nat.mod_lt _ (pow_pos hb _)
    have hdiv : n / b ^ (k + 1) = d := (Finset.mem_filter.mp hn).2
    have hdecomp : n = u + d * b ^ (k + 1) := by
      dsimp [u]
      conv_lhs => rw [← Nat.mod_add_div n (b ^ (k + 1))]
      rw [hdiv]
      ring
    have hdata : u ∈ W b D (k + 1) ∧ d ∈ D ∧ c ≠ d := by
      rw [hdecomp] at hn
      exact (mem_Fiber_append_iff hb hd hu).mp hn
    have hcD : c ∈ D := by
      have hW := (Finset.mem_filter.mp hdata.1).2.1
      have hh := hW k (by omega : k < k + 1)
      simpa [c, Nat.mod_eq_of_lt (top_quotient_lt hb hu)] using hh
    refine ⟨c, Finset.mem_filter.mpr ⟨hcD, hdata.2.2⟩, u, ?_, hdecomp⟩
    exact Finset.mem_filter.mpr ⟨hdata.1, rfl⟩
  · rintro ⟨c, hc, u, hu, rfl⟩
    have hWu : u ∈ W b D (k + 1) := (Finset.mem_filter.mp hu).1
    have hlt : u < b ^ (k + 1) :=
      Finset.mem_range.mp (Finset.mem_filter.mp hWu).1
    have huc : u / b ^ k = c := (Finset.mem_filter.mp hu).2
    have hcd : c ≠ d := (Finset.mem_filter.mp hc).2
    exact (mem_Fiber_append_iff hb hd hlt).mpr ⟨hWu, hdD, huc ▸ hcd⟩

theorem fiber_sum_next {b k d : ℕ} {D : Finset ℕ}
    (hb : 0 < b) (hd : d < b) (hdD : d ∈ D) (f : ℕ → ℂ) :
    (∑ n ∈ Fiber b D (k + 1) d, f n) =
      ∑ c ∈ D.filter (· ≠ d),
        ∑ u ∈ Fiber b D k c, f (u + d * b ^ (k + 1)) := by
  classical
  let T : Finset (Σ _ : ℕ, ℕ) :=
    (D.filter (· ≠ d)).sigma (fun c => Fiber b D k c)
  have hsum :
      (∑ z ∈ T, f (z.2 + d * b ^ (k + 1))) =
        ∑ n ∈ Fiber b D (k + 1) d, f n := by
    apply Finset.sum_bij (fun z _ => z.2 + d * b ^ (k + 1))
    · intro z hz
      obtain ⟨hc, hu⟩ := Finset.mem_sigma.mp hz
      have hWu : z.2 ∈ W b D (k + 1) := (Finset.mem_filter.mp hu).1
      have hlt : z.2 < b ^ (k + 1) :=
        Finset.mem_range.mp (Finset.mem_filter.mp hWu).1
      have huc : z.2 / b ^ k = z.1 := (Finset.mem_filter.mp hu).2
      have hcd : z.1 ≠ d := (Finset.mem_filter.mp hc).2
      exact (mem_Fiber_append_iff hb hd hlt).mpr ⟨hWu, hdD, huc ▸ hcd⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      obtain ⟨hc₁, hu₁⟩ := Finset.mem_sigma.mp hz₁
      obtain ⟨hc₂, hu₂⟩ := Finset.mem_sigma.mp hz₂
      have hu : z₁.2 = z₂.2 := by omega
      have hc : z₁.1 = z₂.1 := by
        have h₁ := (Finset.mem_filter.mp hu₁).2
        have h₂ := (Finset.mem_filter.mp hu₂).2
        rw [← h₁, ← h₂, hu]
      exact Sigma.ext hc (by cases z₁; cases z₂; simp_all)
    · intro n hn
      obtain ⟨c, hc, u, hu, hnEq⟩ :=
        (mem_Fiber_succ_iff hb hd hdD).mp hn
      refine ⟨⟨c, u⟩, Finset.mem_sigma.mpr ⟨hc, hu⟩, ?_⟩
      exact hnEq.symm
    · intro z hz
      rfl
  rw [← hsum, Finset.sum_sigma]

end DigitalAdjacent

end

section

open Finset
open scoped Classical
noncomputable section
namespace DigitalAdjacent

def e (n:ℕ) (t:ℝ) : ℂ := Complex.exp ((((2:ℝ)*Real.pi*((n:ℝ)*t)):ℂ)*Complex.I)
def recSum (b:ℕ) (D:Finset ℕ) (k:ℕ) : ℕ → ℝ → ℂ :=
  Nat.rec (motive:=fun _ : ℕ=>ℕ→ℝ→ℂ) e (fun k prev d t=>
    e (d*b^(k+1)) t * ∑ c∈D.filter (fun c=>c≠d),prev c t) k

theorem add_e (n m:ℕ) (t:ℝ) : e (n+m) t = e m t * e n t := by
  unfold e
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fiber_zero {b d:ℕ} (D:Finset ℕ) (hd:d∈D) (db:d<b) : Fiber b D 0 d = {d} := by
  ext n
  simp only [Fiber,W,mem_filter,mem_range,pow_one,pow_zero,Nat.div_one,
    Nat.lt_one_iff,mem_singleton,forall_eq, Nat.sub_self, Nat.not_lt_zero,
    false_implies, implies_true, and_true]
  constructor
  · intro h
    exact h.2
  · rintro rfl
    simp [db,Nat.mod_eq_of_lt db,hd]

theorem partition {b:ℕ} {D:Finset ℕ} (bp:0<b) (k:ℕ) (f:ℕ→ℂ) :
    ∑n∈W b D (k+1), f n = ∑d∈D, ∑n∈Fiber b D k d,f n := by
  apply Eq.symm
  apply Finset.sum_fiberwise_of_maps_to (g:=fun n:ℕ=>n/b^k)
  intro n hn
  rcases mem_filter.mp hn with ⟨hr,hD,_⟩
  have nl : n/b^k < b := (Nat.div_lt_iff_lt_mul (pow_pos bp k)).mpr (by
    simpa [pow_succ,Nat.mul_comm] using mem_range.mp hr)
  simpa [Nat.mod_eq_of_lt nl] using hD k (by omega)

theorem from_fibers (b:ℕ) (hb:2≤b) (D:Finset ℕ) (sub:D⊆range b)
    (step : ∀ k d, d∈D → ∀ f:ℕ→ℂ, ∑n∈Fiber b D (k+1) d,f n =
      ∑c∈D.filter (fun c=>c≠d),∑n∈Fiber b D k c,f (n+d*b^(k+1))) (k:ℕ) :
    (∀t:ℝ, ∑n∈W b D (k+1),e n t = ∑d∈D,recSum b D k d t) ∧
      (W b D (k+1)).card = D.card*(D.card-1)^k := by
  have rows (j:ℕ) : ∀ d∈D, (∀t:ℝ,∑n∈Fiber b D j d,e n t = recSum b D j d t) ∧
      (Fiber b D j d).card=(D.card-1)^j := by
    induction j with
    | zero =>
      intro d hd
      rw [fiber_zero D hd (mem_range.mp (sub hd))]
      simp [recSum]
    | succ j ih =>
      intro d hd
      constructor
      · intro t
        rw [step j d hd]
        change _ = e (d*b^(j+1)) t * _
        rw [mul_sum]
        apply sum_congr rfl
        intro c hc
        simp only [add_e,←mul_sum,(ih c (mem_filter.mp hc).1).1]
        rfl
      · have h := step j d hd (fun _=>1)
        have cc : (D.filter (fun c=>c≠d)).card=D.card-1 := by
          have eq : D.filter (fun c=>c≠d) = D.erase d := by ext c; simp [and_comm]
          rw [eq,card_erase_of_mem hd]
        have each (c:ℕ) (hc:c∈D.filter (fun c=>c≠d)) : (∑_n∈Fiber b D j c,(1:ℂ)) =
            (((D.card-1)^j:ℕ):ℂ) := by simp [(ih c (mem_filter.mp hc).1).2]
        rw [Finset.sum_congr rfl each] at h
        simp only [sum_const,nsmul_eq_mul,mul_one,cc] at h
        rw [pow_succ,Nat.mul_comm]
        exact_mod_cast h
  constructor
  · intro t
    rw [partition (by omega : 0<b) k]
    exact sum_congr rfl (fun d hd=>(rows k d hd).1 t)
  · have h := partition (D:=D) (by omega : 0<b) k (fun _=>1)
    have each (d:ℕ) (hd:d∈D) : (∑_n∈Fiber b D k d,(1:ℂ)) = (((D.card-1)^k:ℕ):ℂ) := by
      simp [(rows k d hd).2]
    rw [sum_congr rfl each] at h
    simp only [sum_const,nsmul_eq_mul,mul_one] at h
    exact_mod_cast h
end DigitalAdjacent

end
end

set_option maxHeartbeats 1200000 in
theorem Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * (↑x1 * x2)) * Complex.I); have x2 : ℕ → Finset ℕ → ℕ → Finset ℕ := fun (x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ) => {x5 ∈ Finset.range (x2 ^ x4) | (∀ x6 < x4, x5 / x2 ^ x6 % x2 ∈ x3) ∧ ∀ x6 < x4 - (1 : ℕ), x5 / x2 ^ x6 % x2 ≠ x5 / x2 ^ (x6 + (1 : ℕ)) % x2}; have x3 : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : Finset ℕ) (x5 : ℕ) => Nat.rec (motive := fun (x6 : ℕ) => ℕ → ℝ → ℂ) x1 (fun (x6 : ℕ) (x7 : ℕ → ℝ → ℂ) (x8 : ℕ) (x9 : ℝ) => x1 (x8 * x3 ^ (x6 + (1 : ℕ))) x9 * ∑ x10 ∈ x4 with x10 ≠ x8, x7 x10 x9) x5; ∀ (x4 : ℕ), (2 : ℕ) ≤ x4 → ∀ x6 ⊆ Finset.range x4, (2 : ℕ) ≤ x6.card → ∀ (x9 : ℕ), (∀ (x10 : ℝ), ∑ x11 ∈ x2 x4 x6 (x9 + (1 : ℕ)), x1 x11 x10 = ∑ x11 ∈ x6, x3 x4 x6 x9 x11 x10) ∧ (x2 x4 x6 (x9 + (1 : ℕ))).card = x6.card * (x6.card - (1 : ℕ)) ^ x9) := by
  intro phase words recur b hb D sub _ k
  have he : phase = DigitalAdjacent.e := by
    funext n t
    dsimp only [phase,DigitalAdjacent.e]
    push_cast
    ring
  have hw : words = DigitalAdjacent.W := by
    funext b D j
    ext n
    simp only [words, DigitalAdjacent.W, Finset.mem_filter, Finset.mem_range]
  have hr : recur = DigitalAdjacent.recSum := by
    funext b D j d t
    induction j generalizing d with
    | zero =>
      change phase d t = DigitalAdjacent.e d t
      rw [he]
    | succ j ih =>
      change phase (d*b^(j+1)) t * _ = DigitalAdjacent.e (d*b^(j+1)) t * _
      rw [he]
  rw [he,hw,hr]
  exact DigitalAdjacent.from_fibers b hb D sub (fun j d hd f =>
    DigitalAdjacent.fiber_sum_next (b := b) (D := D) (k := j) (d := d)
      (by omega) (Finset.mem_range.mp (sub hd)) hd f) k
