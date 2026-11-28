import Mathlib

namespace CubicWindow

private theorem digit {x k r : ℤ} (hr : |r| < x) (h : x*k+r=0) : r=0 := by
  rcases lt_trichotomy k 0 with hk|hk|hk
  · have := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (show 0 ≤ x by grind [abs_nonneg r])
    grind [abs_lt.mp hr]
  · simp_all
  · have := mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) (show 0 ≤ x by grind [abs_nonneg r])
    grind [abs_lt.mp hr]

private theorem roots {a b c d e f : ℤ}
    (h : a+b+c=d+e+f) (q : a^2+b^2+c^2=d^2+e^2+f^2)
    (t : a^3+b^3+c^3=d^3+e^3+f^3) (z : ℤ) :
    (z-a)*(z-b)*(z-c)=(z-d)*(z-e)*(z-f) := by
  have pair : a*b+b*c+c*a=d*e+e*f+f*d := by
    have sq := congrArg (fun w : ℤ => w^2) h
    linarith only [sq,q]
  have prod : a*b*c=d*e*f := by
    have cube := congrArg (fun w : ℤ => w^3) h
    have cross : (a+b+c)*(a^2+b^2+c^2)=(d+e+f)*(d^2+e^2+f^2) := by rw [h,q]
    linarith only [cube,cross,t]
  linear_combination -z^2*h + z*pair - prod

private theorem matchThree (u v : Fin 3 → ℤ)
    (h : u 0+u 1+u 2=v 0+v 1+v 2)
    (q : u 0^2+u 1^2+u 2^2=v 0^2+v 1^2+v 2^2)
    (t : u 0^3+u 1^3+u 2^3=v 0^3+v 1^3+v 2^3) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i, u i=v (σ i) := by
  have hit := roots h q t (u 0)
  simp only [sub_self, zero_mul] at hit
  rcases (by simpa only [mul_eq_zero, sub_eq_zero] using hit.symm : (u 0=v 0 ∨ u 0=v 1) ∨ u 0=v 2) with (h0|h0)|h0
  · rw [h0] at h q
    have h2 : u 2 = v 1+v 2-u 1 := by omega
    rw [h2] at q
    have hp : (u 1-v 1)*(u 1-v 2)=0 := by linarith only [q]
    rcases mul_eq_zero.mp hp with hj|hj
    · refine ⟨Equiv.refl _, ?_⟩
      intro i
      fin_cases i
      · change u 0 = v 0
        omega
      · change u 1 = v 1
        omega
      · change u 2 = v 2
        omega
    · refine ⟨Equiv.swap 1 2, ?_⟩
      intro i
      fin_cases i
      · change u 0 = v 0
        omega
      · change u 1 = v 2
        omega
      · change u 2 = v 1
        omega
  · rw [h0] at h q
    have h2 : u 2 = v 0+v 2-u 1 := by omega
    rw [h2] at q
    have hp : (u 1-v 0)*(u 1-v 2)=0 := by linarith only [q]
    rcases mul_eq_zero.mp hp with hj|hj
    · refine ⟨Equiv.swap 0 1, ?_⟩
      intro i
      fin_cases i
      · change u 0 = v 1
        omega
      · change u 1 = v 0
        omega
      · change u 2 = v 2
        omega
    · refine ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), ?_⟩
      intro i
      fin_cases i
      · change u 0 = v 1
        omega
      · change u 1 = v 2
        omega
      · change u 2 = v 0
        omega
  · rw [h0] at h q
    have h2 : u 2 = v 0+v 1-u 1 := by omega
    rw [h2] at q
    have hp : (u 1-v 0)*(u 1-v 1)=0 := by linarith only [q]
    rcases mul_eq_zero.mp hp with hj|hj
    · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), ?_⟩
      intro i
      fin_cases i
      · change u 0 = v 2
        omega
      · change u 1 = v 0
        omega
      · change u 2 = v 1
        omega
    · refine ⟨Equiv.swap 0 2, ?_⟩
      intro i
      fin_cases i
      · change u 0 = v 2
        omega
      · change u 1 = v 1
        omega
      · change u 2 = v 0
        omega

end CubicWindow

private theorem momentBound (u : Fin 3 → ℤ) {H : ℕ}
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ H) {k : ℕ} (hk : k ≤ 3) :
    0 ≤ ∑ i, u i^k ∧ ∑ i, u i^k ≤ 3*((H:ℤ)+1)^3 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => pow_nonneg (hu i).1 _
  · calc
      _ ≤ ∑ _i : Fin 3, ((H:ℤ)+1)^3 := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ((H:ℤ)+1)^k := by gcongr; exact (hu i).1; linarith [(hu i).2]
          _ ≤ _ := pow_le_pow_right₀ (by omega) hk
      _ = _ := by simp [Finset.sum_const]

private theorem smallCoefficient (a b c p q r M : ℤ)
    (hp : |p| ≤ M) (hq : |q| ≤ M) (hr : |r| ≤ M) :
    |a*p+b*q+c*r| ≤ (|a|+|b|+|c|)*M := by
  calc
    _ ≤ (|a*p|+|b*q|)+|c*r| := (abs_add_le (a*p+b*q) (c*r)).trans (add_le_add (abs_add_le (a*p) (b*q)) (le_refl |c*r|))
    _ = |a| * |p| + |b| * |q| + |c| * |r| := by simp [abs_mul]
    _ ≤ |a| *M+|b| *M+|c| *M := by gcongr
    _ = _ := by ring

theorem Conjectures.Goldbach.CubicShortIntervalRigidity : (by
  classical
  exact ∀ P : Polynomial ℤ, P.natDegree=3 → ∃ C : ℕ, 0<C ∧ ∀ X H : ℕ, 1≤H → C*(H+1)^3 ≤ X → ∀ a b : Fin 3 → ℕ, (∀ i, a i ∈ Finset.Icc X (X+H) ∧ b i ∈ Finset.Icc X (X+H)) → (∑ i, P.eval ((a i):ℤ)) = (∑ i, P.eval ((b i):ℤ)) → ∃ σ : Equiv.Perm (Fin 3), ∀ i, a i=b (σ i)) := by
  classical
  intro P deg
  let A := P.coeff 3
  let B := P.coeff 2
  let D := P.coeff 1
  have hA : A ≠ 0 := by
    dsimp [A]; rw [← deg]; exact Polynomial.leadingCoeff_ne_zero.mpr (by intro e; simp [e] at deg)
  refine ⟨20*(A.natAbs+B.natAbs+D.natAbs+1), by positivity, ?_⟩
  intro X H hH size a b hab he
  let u (i : Fin 3) : ℤ := a i-X
  let v (i : Fin 3) : ℤ := b i-X
  have rangeUV (i : Fin 3) := hab i
  simp only [Finset.mem_Icc] at rangeUV
  have hu (i) : 0 ≤ u i ∧ u i ≤ H := by dsimp [u]; specialize rangeUV i; omega
  have hv (i) : 0 ≤ v i ∧ v i ≤ H := by dsimp [v]; specialize rangeUV i; omega
  let d (k : ℕ) := (∑ i, u i^k) - (∑ i, v i^k)
  let M : ℤ := 3*((H:ℤ)+1)^3
  have bd (k) (hk : k ≤ 3) : |d k| ≤ M := by
    have := momentBound u hu hk
    have := momentBound v hv hk
    dsimp [M,d]; apply abs_le.mpr; constructor <;> omega
  have hx : 20*(|A|+|B|+|D|+1)*((H:ℤ)+1)^3 ≤ (X:ℤ) := by
    have co := (Int.ofNat_le.mpr size)
    push_cast at co
    simpa [Int.natCast_natAbs] using co
  have pos : 0 < ((H:ℤ)+1)^3 := by positivity
  have large : (3*|A|+2*|B|+|D|)*M < X := by
    dsimp [M]
    nlinarith only [hx, pos, mul_nonneg (abs_nonneg A) pos.le, mul_nonneg (abs_nonneg B) pos.le, mul_nonneg (abs_nonneg D) pos.le]
  have xpos : (0:ℤ) < X := by
    apply lt_of_le_of_lt _ large
    dsimp [M]; positivity
  let r := A*d 3+B*d 2+D*d 1
  let s := 3*A*d 2+2*B*d 1
  have br : |r| < X := by
    apply lt_of_le_of_lt (smallCoefficient A B D _ _ _ M (bd 3 (by decide)) (bd 2 (by decide)) (bd 1 (by decide)))
    apply lt_of_le_of_lt _ large
    gcongr <;> first | positivity | linarith [abs_nonneg A, abs_nonneg B]
  have bs : |s| < X := by
    have e := smallCoefficient (3*A) (2*B) 0 _ _ 0 M (bd 2 (by decide)) (bd 1 (by decide)) (by dsimp [M]; simp; positivity)
    simp [abs_mul] at e
    apply lt_of_le_of_lt e
    apply lt_of_le_of_lt _ large
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg D)) (by dsimp [M]; positivity)
  have ev (y : ℤ) : P.eval y=P.coeff 0+D*y+B*y^2+A*y^3 := by
    rw [Polynomial.eval_eq_sum_range' (n := 4) (by omega)]
    simp [Finset.sum_range_succ,A,B,D]
  have E : (X:ℤ)*(X*(3*A*d 1)+s)+r=0 := by
    simp only [ev, Fin.sum_univ_three] at he
    dsimp [s,r,d,u,v]
    simp only [Fin.sum_univ_three]
    linear_combination he
  have R := CubicWindow.digit br E
  have E' : (X:ℤ)*(3*A*d 1)+s=0 := by
    have hz : (X:ℤ)*(X*(3*A*d 1)+s)=0 := by linarith only [E,R]
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt xpos)
  have S := CubicWindow.digit bs E'
  have one : d 1=0 := by
    have hh : (X:ℤ)*(3*A)*d 1=0 := by linear_combination E'-S
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (ne_of_gt xpos) (mul_ne_zero (by decide) hA))
  have two : d 2=0 := by
    have hh : 3*A*d 2=0 := by simpa [s,one] using S
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by decide) hA)
  have three : d 3=0 := by
    have hh : A*d 3=0 := by simpa [r,one,two] using R
    exact (mul_eq_zero.mp hh).resolve_left hA
  simp only [d, Fin.sum_univ_three, pow_one, sub_eq_zero] at one two three
  obtain ⟨σ,hσ⟩ := CubicWindow.matchThree u v one two three
  refine ⟨σ, fun i => ?_⟩
  specialize hσ i
  dsimp [u,v] at hσ
  omega
