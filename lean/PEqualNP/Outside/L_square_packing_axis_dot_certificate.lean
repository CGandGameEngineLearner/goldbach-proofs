import Mathlib

private lemma dot_abs_lt (A B u v : ℝ) (hu : abs u < 1/2) (hv : abs v < 1/2)
    (hAB : 0 < abs A + abs B) : abs (A*u+B*v) < (abs A + abs B)/2 := by
  have htri : abs (A*u+B*v) ≤ abs A * abs u + abs B * abs v := by
    calc abs (A*u+B*v) ≤ abs (A*u) + abs (B*v) := abs_add_le _ _
      _ = abs A * abs u + abs B * abs v := by rw [abs_mul, abs_mul]
  have hstrict : abs A * abs u + abs B * abs v < (abs A + abs B)/2 := by
    rcases eq_or_lt_of_le (abs_nonneg A) with hA | hA
    · have hA' : abs A = 0 := hA.symm
      have hBpos : 0 < abs B := by rw [hA'] at hAB; linarith
      have h1 : abs B * abs v < abs B * (1/2) := mul_lt_mul_of_pos_left hv hBpos
      rw [hA']
      nlinarith [h1]
    · have h1 : abs A * abs u < abs A * (1/2) := mul_lt_mul_of_pos_left hu hA
      have h2 : abs B * abs v ≤ abs B * (1/2) := mul_le_mul_of_nonneg_left hv.le (abs_nonneg B)
      nlinarith [h1, h2]
  linarith

theorem PEqualNP.Outside.L_square_packing_axis_dot_certificate :
    let rad := fun (a b c s : ℝ) => (|a*c+b*s|+|b*c-a*s|)/2; ∀ a b c s k l x y u v i j m n : ℝ, |i|<1/2 → |j|<1/2 → |m|<1/2 → |n|<1/2 → 0<rad a b c s → 0<rad a b k l → rad a b c s+rad a b k l≤a*(u-x)+b*(v-y) → (x+c*i-s*j,y+s*i+c*j)≠(u+k*m-l*n,v+l*m+k*n) := by
  dsimp only
  intro a b c s k l x y u v i j m n hi hj hm hn h1 h2 hle hEq
  simp only [Prod.mk.injEq] at hEq
  have hx : x + c*i - s*j = u + k*m - l*n := hEq.1
  have hy : y + s*i + c*j = v + l*m + k*n := hEq.2
  have hu : u = x + c*i - s*j - k*m + l*n := by linarith
  have hv : v = y + s*i + c*j - l*m - k*n := by linarith
  have hP : abs ((a*c+b*s)*i + (b*c-a*s)*j) < (abs (a*c+b*s) + abs (b*c-a*s))/2 :=
    dot_abs_lt (a*c+b*s) (b*c-a*s) i j hi hj (by linarith)
  have hQ : abs ((a*k+b*l)*m + (b*k-a*l)*n) < (abs (a*k+b*l) + abs (b*k-a*l))/2 :=
    dot_abs_lt (a*k+b*l) (b*k-a*l) m n hm hn (by linarith)
  have hlin : a*(u-x)+b*(v-y) = ((a*c+b*s)*i + (b*c-a*s)*j) - ((a*k+b*l)*m + (b*k-a*l)*n) := by
    rw [hu, hv]
    ring
  rw [hlin] at hle
  have htri : abs (((a*c+b*s)*i + (b*c-a*s)*j) - ((a*k+b*l)*m + (b*k-a*l)*n)) ≤ abs ((a*c+b*s)*i + (b*c-a*s)*j) + abs ((a*k+b*l)*m + (b*k-a*l)*n) := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le ((a*c+b*s)*i + (b*c-a*s)*j) (-((a*k+b*l)*m + (b*k-a*l)*n))
  have habs : abs (((a*c+b*s)*i + (b*c-a*s)*j) - ((a*k+b*l)*m + (b*k-a*l)*n)) < (abs (a*c+b*s) + abs (b*c-a*s))/2 + (abs (a*k+b*l) + abs (b*k-a*l))/2 := by linarith
  have hlt : ((a*c+b*s)*i + (b*c-a*s)*j) - ((a*k+b*l)*m + (b*k-a*l)*n) < (abs (a*c+b*s) + abs (b*c-a*s))/2 + (abs (a*k+b*l) + abs (b*k-a*l))/2 :=
    lt_of_le_of_lt (le_abs_self _) habs
  linarith
