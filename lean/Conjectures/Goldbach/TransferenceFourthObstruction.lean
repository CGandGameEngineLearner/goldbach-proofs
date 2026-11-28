import Mathlib
import Conjectures.Goldbach.PolynomialFourierTransference

/-!
Sample k points independently and uniformly in a prime cyclic group and use
their multiplicities as a density of mean one. Orthogonality gives its fourth
and sixth moments at each nonzero frequency. A single averaged score then
selects a sample with bounded fourth moment and small Fourier coefficients.
The sumset of the support occupies at most half the group.

The Fourier normalization follows PolynomialFourierTransference (PR #4281).
-/

namespace FourthObstruction
open Finset PolynomialTransfer
open scoped ComplexConjugate

private theorem phase_pow {N : ℕ} [NeZero N] (r x : ZMod N) (j : ℕ) :
    ch r x ^ j = ch ((j : ZMod N)*r) x := by
  induction j with
  | zero => simp [ch]
  | succ j ih =>
    rw [pow_succ, ih]
    unfold ch
    rw [← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    ring

/-- Orthogonality of the modes 0,r,2r,3r, which are distinct modulo N. -/
private theorem phase_orth {N : ℕ} [Fact N.Prime] (hN : 5 ≤ N) (r : ZMod N) (hr : r ≠ 0)
    (i j : ℕ) (hi : i < 4) (hj : j < 4) :
    C (fun x => ch r x ^ i * conj (ch r x ^ j)) =
      if i=j then (1:ℂ) else 0 := by
  classical
  simp_rw [phase_pow, csub]
  have h := Fone ((i : ZMod N)*r - (j : ZMod N)*r)
  simp only [F, Complex.ofReal_one, one_mul] at h
  rw [h]
  have hij : (i : ZMod N)*r - (j : ZMod N)*r = 0 ↔ i=j := by
    rw [sub_eq_zero, mul_left_inj' hr]
    constructor
    · intro h
      have eq := congrArg ZMod.val h
      simpa only [ZMod.val_natCast_of_lt (by omega : i<N), ZMod.val_natCast_of_lt (by omega : j<N)] using eq
    · rintro rfl; rfl
  simp only [hij]

private theorem phase_parse {N : ℕ} [Fact N.Prime] (hN : 5 ≤ N) (r : ZMod N) (hr : r ≠ 0)
    (d : ℕ) (hd : d ≤ 3) (c : ℕ → ℂ) :
    E (fun x => ‖∑ i ∈ range (d+1), c i * ch r x ^ i‖^2) =
      ∑ i ∈ range (d+1), ‖c i‖^2 := by
  classical
  apply Complex.ofReal_injective
  rw [← Cof]
  simp only [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, map_mul, sum_mul_sum]
  calc
    _ = C (fun x => ∑ i ∈ range (d+1), ∑ j ∈ range (d+1),
        (c i*conj (c j)) * (ch r x ^ i * conj (ch r x ^ j))) := by
      congr 1
      funext x
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      ring
    _ = _ := by
      rw [Csum, Complex.ofReal_sum]
      apply sum_congr rfl
      intro i hi
      rw [Csum]
      simp only [Cmul]
      have HH (j : ℕ) (hj : j ∈ range (d+1)) := phase_orth hN r hr i j
        (by have := mem_range.mp hi; omega) (by have := mem_range.mp hj; omega)
      apply Eq.trans (sum_congr rfl (fun j hj => by rw [HH j hj]))
      simp [mul_ite, hi, Complex.mul_conj']

private theorem phase_step {N : ℕ} [Fact N.Prime] (hN : 5 ≤ N) (r : ZMod N) (hr : r ≠ 0)
    (z : ℂ) (d : ℕ) (hd : d ≤ 3) :
    (∑ x : ZMod N, ‖z + ch r x‖ ^ (d*2)) =
      (N:ℝ) * ∑ i ∈ range (d+1), (‖z‖^(d-i) * (d.choose i : ℝ))^2 := by
  let c (i : ℕ) : ℂ := z^(d-i)*(d.choose i:ℂ)
  have he (x : ZMod N) : (z+ch r x)^d = ∑ i ∈ range (d+1), c i * ch r x ^ i := by
    rw [add_comm, add_pow]
    apply sum_congr rfl; intro i _; dsimp [c]; ring
  have h := phase_parse hN r hr d hd c
  change (∑ x : ZMod N, ‖∑ i ∈ range (d+1), c i * ch r x ^ i‖^2) / (N : ℝ) = _ at h
  simp only [← he, norm_pow, ← pow_mul] at h
  have eq := (div_eq_iff (NeZero.ne (N:ℝ))).mp h
  simpa [c, norm_mul, norm_pow, Complex.norm_natCast, mul_comm] using eq

theorem phase_step_two {N : ℕ} [Fact N.Prime] (hN : 5 ≤ N) (r : ZMod N) (hr : r ≠ 0) (z : ℂ) :
    (∑ x : ZMod N, ‖z + ch r x‖^2) = (N:ℝ) * (‖z‖^2+1) := by
  simpa [sum_range_succ] using phase_step hN r hr z 1 (by decide)

theorem phase_step_four {N : ℕ} [Fact N.Prime] (hN : 5 ≤ N) (r : ZMod N) (hr : r ≠ 0) (z : ℂ) :
    (∑ x : ZMod N, ‖z + ch r x‖^4) = (N:ℝ) * (‖z‖^4+4*‖z‖^2+1) := by
  rw [show (4:ℕ)=2*2 by decide, phase_step hN r hr z 2 (by decide)]
  congr 1
  norm_num [sum_range_succ, Nat.choose]; ring

theorem phase_step_six {N : ℕ} [Fact N.Prime] (hN : 5 ≤ N) (r : ZMod N) (hr : r ≠ 0) (z : ℂ) :
    (∑ x : ZMod N, ‖z + ch r x‖^6) = (N:ℝ) * (‖z‖^6+9*‖z‖^4+9*‖z‖^2+1) := by
  rw [show (6:ℕ)=3*2 by decide, phase_step hN r hr z 3 (by decide)]
  congr 1
  norm_num [sum_range_succ, Nat.choose]; ring

end FourthObstruction

namespace FourthObstruction

open Finset

private theorem sample_step {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (k : ℕ) (g : ℂ → ℝ) :
    (∑ u : Fin (k+1) → ZMod N, g (∑ i, f (u i))) =
      ∑ u : Fin k → ZMod N, ∑ x : ZMod N, g ((∑ i, f (u i)) + f x) := by
  let e := Fin.consEquiv (fun _ : Fin (k+1) => ZMod N)
  calc
    _ = ∑ a : ZMod N × (Fin k → ZMod N), g (∑ i, f ((e a) i)) :=
      (e.sum_comp (fun u => g (∑ i, f (u i)))).symm
    _ = ∑ x : ZMod N, ∑ u : Fin k → ZMod N, g ((∑ i, f (u i)) + f x) := by
      rw [Fintype.sum_prod_type]
      simp only [e, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_comm]
    _ = _ := sum_comm

/-- Unnormalized phase moments for independent uniform coordinates. -/
theorem sample_moments {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (h2 : ∀ z : ℂ, (∑ x : ZMod N, ‖z + f x‖^2) = (N:ℝ)*(‖z‖^2+1))
    (h4 : ∀ z : ℂ, (∑ x : ZMod N, ‖z + f x‖^4) = (N:ℝ)*(‖z‖^4+4*‖z‖^2+1))
    (h6 : ∀ z : ℂ, (∑ x : ZMod N, ‖z + f x‖^6) = (N:ℝ)*(‖z‖^6+9*‖z‖^4+9*‖z‖^2+1))
    (k : ℕ) :
    (∑ u : Fin k → ZMod N, ‖∑ i, f (u i)‖^2) = (N:ℝ)^k*k ∧
    (∑ u : Fin k → ZMod N, ‖∑ i, f (u i)‖^4) ≤ (N:ℝ)^k*(2*(k:ℝ)^2) ∧
    (∑ u : Fin k → ZMod N, ‖∑ i, f (u i)‖^6) ≤ (N:ℝ)^k*(6*(k:ℝ)^3) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨ih2, ih4, ih6⟩ := ih
    let W (u : Fin k → ZMod N) : ℂ := ∑ i, f (u i)
    have step (e : ℕ) :
        (∑ u : Fin (k+1) → ZMod N, ‖∑ i, f (u i)‖^e) =
        ∑ u : Fin k → ZMod N, ∑ x : ZMod N, ‖W u + f x‖^e :=
      sample_step f k (fun z => ‖z‖^e)
    change (∑ u, ‖W u‖^2) = _ at ih2
    change (∑ u, ‖W u‖^4) ≤ _ at ih4
    change (∑ u, ‖W u‖^6) ≤ _ at ih6
    have hc : (∑ _u : Fin k → ZMod N, (1:ℝ)) = (N:ℝ)^k := by simp
    rw [step 2, step 4, step 6]
    simp only [h2, h4, h6, ← mul_sum, sum_add_distrib, hc, ih2]
    rw [pow_succ (N:ℝ) k, Nat.cast_succ]
    refine ⟨by ring, ?_, ?_⟩
    · calc
        _ ≤ (N:ℝ)*((N:ℝ)^k*(2*(k:ℝ)^2) + 4*((N:ℝ)^k*k) + (N:ℝ)^k) := by gcongr
        _ = (N:ℝ)^k*N*(2*(k:ℝ)^2+4*k+1) := by ring
        _ ≤ _ := by gcongr; nlinarith
    · calc
        _ ≤ (N:ℝ)*((N:ℝ)^k*(6*(k:ℝ)^3) + 9*((N:ℝ)^k*(2*(k:ℝ)^2)) +
              9*((N:ℝ)^k*k) + (N:ℝ)^k) := by gcongr
        _ = (N:ℝ)^k*N*(6*(k:ℝ)^3+18*(k:ℝ)^2+9*k+1) := by ring
        _ ≤ _ := by gcongr; nlinarith [Nat.cast_nonneg (α := ℝ) k]

end FourthObstruction

namespace FourthObstruction
open Finset PolynomialTransfer
open scoped Classical
noncomputable section
variable {N k : ℕ} [NeZero N]

def weight (u : Fin k → ZMod N) (x : ZMod N) : ℝ :=
  ∑ i, if u i = x then (N:ℝ)/k else 0

omit [NeZero N] in
theorem weight_nonneg (u : Fin k → ZMod N) (x : ZMod N) : 0 ≤ weight u x :=
  sum_nonneg (fun i _ => by split_ifs <;> positivity)

theorem weight_mean (u : Fin k → ZMod N) (hk : 0 < k) : E (weight u) = 1 := by
  simp only [E,weight]
  rw [sum_comm]
  simp [NeZero.ne (N:ℝ), Nat.cast_ne_zero.mpr hk.ne', mul_div_cancel₀]

theorem weight_fourier (u : Fin k → ZMod N) (r : ZMod N) :
    F (weight u) r = (∑ i, ch r (u i)) / (k:ℂ) := by
  unfold F C weight
  simp only [Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_zero, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true, ← mul_sum]
  field_simp [NeZero.ne (N:ℂ)]

theorem weight_centered_zero (u : Fin k → ZMod N) (hk : 0 < k) :
    F (fun x => weight u x - 1) 0 = 0 := by
  rw [Fsub, Fzero, weight_mean u hk, Fone]
  simp

theorem weight_centered_ne (u : Fin k → ZMod N) (r : ZMod N) (hr : r ≠ 0) :
    F (fun x => weight u x - 1) r = (∑ i, ch r (u i)) / (k:ℂ) := by
  rw [Fsub, Fone, ite_eq_right hr, sub_zero, weight_fourier]

theorem weight_support (u : Fin k → ZMod N) :
    (univ.filter (fun x => weight u x ≠ 0)).card ≤ k := by
  have sub : univ.filter (fun x => weight u x ≠ 0) ⊆ univ.image u := by
    intro x hx
    by_contra h
    have hne (i : Fin k) : u i ≠ x := fun eq => h (mem_image.mpr ⟨i,mem_univ _, eq⟩)
    exact (mem_filter.mp hx).2 (by simp [weight,hne])
  exact (card_le_card sub).trans (card_image_le.trans_eq (by simp))

theorem weight_zeros (u : Fin k → ZMod N) (h : 2*k^2 ≤ N) :
    (N:ℝ)/2 ≤ ((univ.filter (fun n : ZMod N =>
      (∑ x, weight u x * weight u (n-x)) = 0)).card:ℝ) := by
  let A := univ.filter (fun x => weight u x ≠ 0)
  let S := image₂ (· + ·) A A
  have hs : S.card ≤ k^2 :=
    (card_image₂_le _ _ _).trans (by simpa only [pow_two] using Nat.mul_le_mul (weight_support u) (weight_support u))
  have hz : (Sᶜ : Finset (ZMod N)) ⊆
      univ.filter fun n : ZMod N => (∑ x, weight u x * weight u (n-x)) = 0 := by
    intro n hn
    refine mem_filter.mpr ⟨mem_univ _, sum_eq_zero (fun x _ => ?_)⟩
    by_contra! hprod
    obtain ⟨hx,hy⟩ := mul_ne_zero_iff.mp hprod
    have sums : x+(n-x) ∈ S := mem_image₂_of_mem
      (mem_filter.mpr ⟨mem_univ _,hx⟩ : x ∈ A)
      (mem_filter.mpr ⟨mem_univ _,hy⟩ : n-x ∈ A)
    exact (mem_compl.mp hn) (by simpa using sums)
  have hc := card_le_card hz
  rw [card_compl, ZMod.card] at hc
  have hc' : N ≤ (univ.filter (fun n : ZMod N =>
      (∑ x, weight u x * weight u (n-x)) = 0)).card * 2 := by omega
  exact (div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast hc')

end
end FourthObstruction

namespace FourthObstruction
open Finset

private theorem parameters (ε : ℝ) (hε : 0 < ε) (T : ℕ) :
    ∃ k N : ℕ, 2 ≤ k ∧ 5 ≤ N ∧ T ≤ N ∧ N.Prime ∧ 2*k^2 ≤ N ∧ N ≤ 4*k^2 ∧
      48 ≤ (k:ℝ)*ε^6 := by
  obtain ⟨j, hj⟩ := exists_nat_ge (48 / ε^6)
  let k := max j (max T 2)
  have hk : 2 ≤ k := (le_max_right _ _).trans (le_max_right _ _)
  have hT : T ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  have hsize : 48 ≤ (k:ℝ)*ε^6 := (div_le_iff₀ (pow_pos hε 6)).mp
    (hj.trans (by exact_mod_cast (show j ≤ k from le_max_left _ _)))
  obtain ⟨N, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2*k^2) (by positivity)
  exact ⟨k,N,hk,by nlinarith,hT.trans (by nlinarith),hp,hlo.le,by omega,hsize⟩

private theorem select_sample {U I : Type*} [Fintype U] [Nonempty U] [DecidableEq I]
    (R : Finset I) (b : U → I → ℝ) (hn : ∀ u r, 0 ≤ b u r)
    (k : ℝ) (hk : 0 < k) (hR : (R.card:ℝ) ≤ 4*k^2) (ε : ℝ) (hε : 0 < ε)
    (hsize : 48 ≤ k*ε^6)
    (h4 : ∀ r ∈ R, (∑ u, b u r ^ 4) ≤ (Fintype.card U : ℝ)*(2/k^2))
    (h6 : ∀ r ∈ R, (∑ u, b u r ^ 6) ≤ (Fintype.card U : ℝ)*(6/k^3)) :
    ∃ u, (∑ r ∈ R, b u r ^ 4) ≤ 16 ∧ ∀ r ∈ R, b u r ≤ ε := by
  classical
  let V : ℝ := Fintype.card U
  let A (u : U) := ∑ r ∈ R, b u r ^ 4
  let B (u : U) := ∑ r ∈ R, b u r ^ 6
  have hv : 0 ≤ V := Nat.cast_nonneg _
  have total (l : ℕ) (q : ℝ) (hq : 0 ≤ q)
      (hp : ∀ r ∈ R, (∑ u, b u r ^ l) ≤ V*q) :
      (∑ u, ∑ r ∈ R, b u r^l) ≤ (4*k^2)*(V*q) := by
    rw [sum_comm]
    calc
      _ ≤ ∑ _r ∈ R, V*q := sum_le_sum hp
      _ = (R.card:ℝ)*(V*q) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hR (mul_nonneg hv hq)
  have ta : (∑ u, A u) ≤ V*8 := by
    refine (total 4 (2/k^2) (by positivity) h4).trans_eq ?_
    field_simp
    ring
  have tb : (∑ u, B u) ≤ V*(24/k) := by
    refine (total 6 (6/k^3) (by positivity) h6).trans_eq ?_
    field_simp
    ring
  have eb : (∑ u, B u) / ε^6 ≤ V/2 := by
    apply (div_le_iff₀ (pow_pos hε _)).mpr
    apply le_trans tb
    have hq : 24/k ≤ ε^6/2 := (div_le_iff₀ hk).mpr (by linarith)
    calc V * (24/k) ≤ V * (ε^6/2) := mul_le_mul_of_nonneg_left hq hv
         _ = _ := by ring
  let score (u : U) := A u / 16 + B u / ε^6
  have budget : (∑ u, score u) ≤ V := by
    simp only [score,sum_add_distrib,← sum_div]
    linarith
  obtain ⟨u, hu⟩ : ∃ u, score u ≤ 1 := by
    by_contra! fail
    have strict := sum_lt_sum_of_nonempty (s := (univ : Finset U)) univ_nonempty
      (f := fun _ => (1:ℝ)) (g := score) (fun u _ => fail u)
    have hvlt : V < ∑ u, score u := by simpa [V] using strict
    exact (not_lt_of_ge budget) hvlt
  have ha : 0 ≤ A u := sum_nonneg (fun _ _ => by positivity)
  have hb : 0 ≤ B u := sum_nonneg (fun _ _ => by positivity)
  change A u/16 + B u/ε^6 ≤ 1 at hu
  refine ⟨u, by linarith [div_nonneg hb (pow_pos hε 6).le], ?_⟩
  intro r hr
  have hBr : b u r ^ 6 ≤ B u := single_le_sum (f := fun r => b u r ^ 6) (fun r _ => by positivity) hr
  have hB : B u / ε^6 ≤ 1 := by linarith
  have hr6 := hBr.trans ((div_le_iff₀ (pow_pos hε _)).mp hB)
  exact (pow_le_pow_iff_left₀ (hn u r) hε.le (by decide : (6:ℕ) ≠ 0)).mp (by simpa using hr6)
end FourthObstruction

open FourthObstruction PolynomialTransfer Finset

theorem Conjectures.Goldbach.TransferenceFourthObstruction : (
by
  classical
  exact ∃ M : ℝ, 0 < M ∧ ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, ∃ N : ℕ, ∃ hN : Nat.Prime N, T ≤ N ∧ (letI : NeZero N := ⟨hN.ne_zero⟩; ∃ f : ZMod N → ℝ,
    let ft := fun (h : ZMod N → ℝ) (r : ZMod N) => (∑ x : ZMod N, (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)
    (∀ x, 0 ≤ f x) ∧ (∑ x, f x)/(N:ℝ)=1 ∧ (∑ r : ZMod N, ‖ft f r‖^4) ≤ M ∧ (∀ r, ‖ft (fun x => f x-1) r‖ ≤ ε) ∧ (N:ℝ)/2 ≤ ((Finset.univ.filter (fun n : ZMod N => (∑ x, f x*f (n-x))=0)).card:ℝ))
) := by
  classical
  refine ⟨17, by norm_num, ?_⟩
  intro ε hε T
  obtain ⟨k,N,hk,hN,hT,hp,hlo,hhi,hsize⟩ := parameters ε hε T
  let _ : Fact N.Prime := ⟨hp⟩
  let _ : NeZero N := ⟨hp.ne_zero⟩
  have hk' : 0 < k := by omega
  have pk : (0:ℝ) < k := by exact_mod_cast hk'
  let R := (univ : Finset (ZMod N)).erase 0
  let b (u : Fin k → ZMod N) (r : ZMod N) := ‖∑ i, ch r (u i)‖ / (k:ℝ)
  have hc : (Fintype.card (Fin k → ZMod N) : ℝ) = (N:ℝ)^k := by simp
  have hR : (R.card : ℝ) ≤ 4*(k:ℝ)^2 := by
    exact_mod_cast (show R.card ≤ 4*k^2 from
      (card_le_univ R).trans ((ZMod.card N).le.trans hhi))
  have moments (r : ZMod N) (hr : r ∈ R) :=
    sample_moments (ch r) (phase_step_two hN r (mem_erase.mp hr).1)
      (phase_step_four hN r (mem_erase.mp hr).1) (phase_step_six hN r (mem_erase.mp hr).1) k
  have normalized (s : ℕ) (C : ℝ) (r : ZMod N)
      (h : (∑ u : Fin k → ZMod N, ‖∑ i, ch r (u i)‖^(2*s)) ≤ (N:ℝ)^k * (C*(k:ℝ)^s)) :
      (∑ u : Fin k → ZMod N, b u r ^ (2*s)) ≤
        (Fintype.card (Fin k → ZMod N):ℝ) * (C/(k:ℝ)^s) := by
    simp only [b,div_pow,← sum_div,hc]
    apply (div_le_iff₀ (pow_pos pk _)).mpr
    refine h.trans_eq ?_
    rw [show 2*s = s+s by omega, pow_add]
    field_simp
  have h4 (r : ZMod N) (hr : r ∈ R) := normalized 2 2 r (moments r hr).2.1
  have h6 (r : ZMod N) (hr : r ∈ R) := normalized 3 6 r (moments r hr).2.2
  obtain ⟨u, hu, hu'⟩ := select_sample R b (fun u r => by dsimp [b]; positivity)
    (k:ℝ) pk hR ε hε hsize h4 h6
  refine ⟨N,hp,hT,weight u,weight_nonneg u,weight_mean u hk',?_,?_,weight_zeros u hlo⟩
  · simp only [← expForm]
    have hb (r : ZMod N) : ‖F (weight u) r‖ = b u r := by
      rw [weight_fourier,norm_div,Complex.norm_natCast]
    rw [← add_sum_erase (a := 0) (s := univ) (fun r => ‖F (weight u) r‖^4) (mem_univ _)]
    rw [Fzero, weight_mean u hk']
    simp only [Complex.ofReal_one,norm_one,one_pow,hb]
    linarith
  · intro r
    simp only [← expForm]
    by_cases hr : r=0
    · subst r
      rw [weight_centered_zero u hk', norm_zero]
      exact hε.le
    · rw [weight_centered_ne u r hr,norm_div,Complex.norm_natCast]
      exact hu' r (mem_erase.mpr ⟨hr,mem_univ _⟩)
