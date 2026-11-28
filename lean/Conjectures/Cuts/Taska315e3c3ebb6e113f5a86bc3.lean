import Mathlib

/-! Orthogonality on the p lifts of a residue class removes its constant row mean. -/

namespace LiftPhase
open Finset

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)

noncomputable def phase (p : ℕ) (a : ℤ) (k : ℕ) : ℂ :=
  E ((k:ℝ) * ((a:ℝ) / ((p^2:ℕ):ℝ)))

theorem phase_norm (p : ℕ) (a : ℤ) (k : ℕ) : ‖phase p a k‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem E_add (x y : ℝ) : E (x+y) = E x * E y := by
  unfold E
  rw [←Complex.exp_add]
  congr 1; push_cast; ring

private theorem E_nat_mul (k : ℕ) (x : ℝ) : E ((k:ℝ)*x) = E x ^ k := by
  unfold E
  rw [←Complex.exp_nat_mul]
  congr 1; push_cast; ring

private theorem E_int (a : ℤ) : E (a:ℝ) = 1 := by
  calc
    _ = Complex.exp ((a:ℂ)*(2*(Real.pi:ℂ)*Complex.I)) := by
      unfold E
      congr 1; push_cast; ring
    _ = _ := Complex.exp_int_mul_two_pi_mul_I a

theorem phase_mod (p : ℕ) (a : ℤ) (k : ℕ) (hp : 0 < p) :
    phase p a (k % p^2) = phase p a k := by
  let q := p^2
  let z := E ((a:ℝ)/(q:ℝ))
  have hq : (q:ℝ) ≠ 0 := by exact_mod_cast (pow_pos hp 2).ne'
  have hz : z^q = 1 := by
    dsimp only [z]
    rw [← E_nat_mul, show (q:ℝ)*((a:ℝ)/(q:ℝ)) = (a:ℝ) by field_simp]
    exact E_int _
  change E (((k % q:ℕ):ℝ)*((a:ℝ)/(q:ℝ))) = E ((k:ℝ)*((a:ℝ)/(q:ℝ)))
  simp only [E_nat_mul]
  change z^(k % q) = z^k
  calc
    _ = z^(q*(k/q) + k % q) := by rw [pow_add,pow_mul,hz,one_pow,one_mul]
    _ = _ := by rw [Nat.div_add_mod]

/-- In a single residue class modulo p, the lifts modulo p² run through
an entire geometric progression with a primitive pth root as ratio. -/
theorem row_zero (p : ℕ) (a : ℤ) (c : ℕ) (hp : p.Prime) (hc : a.natAbs.Coprime (p^2)) :
    (∑ j ∈ range p, phase p a (c+p*j)) = 0 := by
  let z := E ((a:ℝ)/(p:ℝ))
  have hpr : IsPrimitiveRoot z p := by
    have h : a.natAbs.Coprime p := hc.of_dvd_right (dvd_pow_self p (by decide : 2 ≠ 0))
    have hz : z = Complex.exp (2*(Real.pi:ℂ)*Complex.I*((a:ℂ)/(p:ℂ))) := by
      dsimp only [z,E]
      congr 1; push_cast; ring
    rw [hz]
    apply Complex.isPrimitiveRoot_exp_of_isCoprime a p hp.ne_zero
    exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using h)
  have term (j : ℕ) : phase p a (c+p*j) = phase p a c * z^j := by
    dsimp only [phase,z]
    rw [← E_nat_mul, ← E_add]
    congr 1
    push_cast
    field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  simp_rw [term, ← mul_sum, hpr.geom_sum_eq_zero hp.one_lt, mul_zero]

end LiftPhase

namespace LiftRows

open Finset

noncomputable def mass (w : ℕ → ℝ) (X p c j : ℕ) :=
  ∑ m ∈ (range X).filter (fun m : ℕ => m % p^2 = c+p*j), w m

private theorem residue_rows (p : ℕ) (hp : 0 < p) (G : ℕ → ℂ) :
    (∑ r ∈ range (p^2), G r) = ∑ c ∈ range p, ∑ j ∈ range p, G (c+p*j) := by
  let decode (v : ℕ × ℕ) := v.1 + p*v.2
  let encode (r : ℕ) := (r % p, r/p)
  have section_prop (r : ℕ) : decode (encode r) = r := Nat.mod_add_div r p
  have retract (v : ℕ × ℕ) (hv : v ∈ (range p ×ˢ range p)) : encode (decode v) = v := by
    have h := mem_range.mp (mem_product.mp hv).1
    simp [encode, decode, Nat.add_mul_div_left _ _ hp, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
  have mapin (r : ℕ) (hr : r ∈ range (p^2)) : encode r ∈ range p ×ˢ range p := by
    exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hp), mem_range.mpr
      ((Nat.div_lt_iff_lt_mul hp).mpr (by simpa [pow_two] using mem_range.mp hr))⟩
  calc
    _ = ∑ v ∈ range p ×ˢ range p, G (decode v) := by
      apply sum_bij (fun r _ => encode r) mapin
      · intro r _ s _ he
        simpa only [section_prop] using congrArg decode he
      · intro v hv
        refine ⟨decode v, mem_range.mpr ?_, retract v hv⟩
        have h0 := mem_range.mp (mem_product.mp hv).1
        have h1 := mem_range.mp (mem_product.mp hv).2
        change v.1+p*v.2 < p^2
        nlinarith [Nat.mul_le_mul_left p (show v.2+1 ≤ p by omega)]
      · intro r _
        rw [section_prop]
    _ = _ := sum_product _ _ _

theorem reindex (p X : ℕ) (hp : 0 < p) (w : ℕ → ℝ) (F : ℕ → ℂ)
    (hF : ∀ k, F (k % p^2) = F k) :
    (∑ m ∈ range X, (w m:ℂ)*F m) =
      ∑ c ∈ range p, ∑ j ∈ range p, (mass w X p c j:ℂ)*F (c+p*j) := by
  let G (r : ℕ) := ((∑ m ∈ (range X).filter (fun m : ℕ => m % p^2 = r), w m : ℝ):ℂ) * F r
  have maps (m : ℕ) (_ : m ∈ range X) : m % p^2 ∈ range (p^2) :=
    mem_range.mpr (Nat.mod_lt _ (pow_pos hp _))
  calc
    _ = ∑ r ∈ range (p^2), ∑ m ∈ (range X).filter (fun m : ℕ => m % p^2=r), (w m:ℂ)*F m :=
      (sum_fiberwise_of_maps_to maps (fun m => (w m:ℂ)*F m)).symm
    _ = ∑ r ∈ range (p^2), G r := by
      apply sum_congr rfl
      intro r _
      simp only [G, Complex.ofReal_sum, sum_mul]
      apply sum_congr rfl
      intro m hm
      rw [← hF m, (mem_filter.mp hm).2]
    _ = _ := residue_rows p hp G

end LiftRows

namespace LiftCS
open Finset

theorem bound (p : ℕ) (R : ℕ → ℕ → ℝ) (F : ℕ → ℕ → ℂ)
    (habs : ∀ c j, ‖F c j‖ = 1) (cancel : ∀ c, ∑ j ∈ range p, F c j = 0) :
    ‖∑ c ∈ range p, ∑ j ∈ range p, (R c j : ℂ)*F c j‖ ≤
      (p:ℝ)*Real.sqrt (∑ c ∈ range p, ∑ j ∈ range p,
        (R c j - (∑ k ∈ range p, R c k)/(p:ℝ))^2) := by
  let mean (c : ℕ) := (∑ k ∈ range p,R c k)/(p:ℝ)
  let d (c j : ℕ) := R c j - mean c
  have center (c : ℕ) :
      (∑ j ∈ range p, (R c j:ℂ)*F c j) = ∑ j ∈ range p, (d c j:ℂ)*F c j := by
    simp only [d,Complex.ofReal_sub,sub_mul,sum_sub_distrib,←mul_sum,cancel,mul_zero,sub_zero]
  have row_bound (c : ℕ) :
      ‖∑ j ∈ range p, (d c j:ℂ)*F c j‖ ≤ ∑ j ∈ range p, |d c j| := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,habs,mul_one] using
      norm_sum_le (range p) (fun j => (d c j:ℂ)*F c j)
  let s := range p ×ˢ range p
  have cs := sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun t => |d t.1 t.2|)
  have hs : (∑ c ∈ range p, ∑ j ∈ range p, |d c j|)^2 ≤
      ((p:ℝ)*(p:ℝ)) * ∑ c ∈ range p, ∑ j ∈ range p, (d c j)^2 := by
    simpa [s,sum_product,sq_abs] using cs
  calc
    _ = ‖∑ c ∈ range p, ∑ j ∈ range p, (d c j:ℂ)*F c j‖ := by simp_rw [center]
    _ ≤ ∑ c ∈ range p, ‖∑ j ∈ range p, (d c j:ℂ)*F c j‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ range p, ∑ j ∈ range p, |d c j| := sum_le_sum fun c _ => row_bound c
    _ ≤ _ := by
      have hh := Real.sqrt_le_sqrt hs
      rw [Real.sqrt_sq (sum_nonneg fun c _ => sum_nonneg fun j _ => abs_nonneg (d c j)),
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ p*p),Real.sqrt_mul_self (Nat.cast_nonneg p)] at hh
      exact hh

end LiftCS

theorem Conjectures.Cuts.Taska315e3c3ebb6e113f5a86bc3 : (have x1 : (ℕ → ℝ) → ℕ → ℝ → ℂ := fun (x1 : ℕ → ℝ) (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range x2, ↑(x1 x4) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x4 * x3) * Complex.I); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) =>   have x5 : ℕ → ℕ → ℝ := fun (x5 x6 : ℕ) => ∑ x7 ∈ Finset.range x3 with x7 % x4 ^ (2 : ℕ) = x5 + x4 * x6, x2 x7;   ∑ x6 ∈ Finset.range x4, ∑ x7 ∈ Finset.range x4, (x5 x6 x7 - (∑ x8 ∈ Finset.range x4, x5 x6 x8) / ↑x4) ^ (2 : ℕ); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ) (x6 : ℤ), Nat.Prime x5 → x6.natAbs.Coprime (x5 ^ (2 : ℕ)) → ‖x1 x3 x4 (↑x6 / ↑(x5 ^ (2 : ℕ)))‖ ≤ ↑x5 * √(x2 x3 x4 x5)) := by
  classical
  intro S V w X p a hp hcop
  have rearrange : S w X ((a:ℝ)/((p^2:ℕ):ℝ)) =
      ∑ c ∈ Finset.range p, ∑ j ∈ Finset.range p,
        (LiftRows.mass w X p c j : ℂ) * LiftPhase.phase p a (c+p*j) := by
    calc
      _ = ∑ m ∈ Finset.range X, (w m : ℂ) * LiftPhase.phase p a m := by
        dsimp only [S, LiftPhase.phase, LiftPhase.E]
        simp only [mul_assoc]
      _ = _ := LiftRows.reindex p X hp.pos w (LiftPhase.phase p a)
         (fun k => LiftPhase.phase_mod p a k hp.pos)
  rw [rearrange]
  exact LiftCS.bound p (LiftRows.mass w X p) (fun c j => LiftPhase.phase p a (c+p*j))
    (fun c j => LiftPhase.phase_norm p a (c+p*j))
    (fun c => LiftPhase.row_zero p a c hp hcop)
