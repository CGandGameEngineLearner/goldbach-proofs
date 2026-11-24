import Mathlib

-- Sketch: for a zero-sum triple u+v+w=0 one has u*v = w^2 - (u^2+u*v+v^2), hence
-- a*b*c = (c^2-S)*c and x*y*z = (z^2-S)*z for the common norm
-- S = a^2+a*b+b^2 = x^2+x*y+y^2, so x*y*z - a*b*c = (z-c)*(z^2+z*c+c^2-S).
-- Writing b = -(a+c) rewrites S = a^2+a*c+c^2; from -2*c ≤ a ≤ 0 one gets
-- a^2+a*c ≤ 2*c^2, while z ≥ c+1 and c ≥ 0 give z^2+z*c ≥ 2*c^2+3*c+1 > 2*c^2,
-- so both factors of (z-c)*(z^2+z*c+c^2-S) are positive.
theorem PEqualNP.Outside.L_hash_collision_lab_ordered_product :
    ∀ a b c x y z : ℤ, a≤b → b≤c → x≤y → y≤z → a+b+c=0 → x+y+z=0 → a^2+a*b+b^2=x^2+x*y+y^2 → c<z → a*b*c<x*y*z := by
  intro a b c x y z h1 h2 h3 h4 h5 h6 h7 h8
  -- linear consequences of the orderings and the zero-sum conditions
  have hc0 : 0 ≤ c := by omega
  have hac : a ≤ c := by omega
  have ha1 : -2 * c ≤ a := by omega
  have hb_eq : b = -(a + c) := by omega
  have hz1 : c + 1 ≤ z := by omega
  -- a^2 + a*c ≤ 2*c^2, with certificate (a + 2*c) * (c - a) ≥ 0
  have hexpand1 : (a + 2 * c) * (c - a) = 2 * c ^ 2 - a ^ 2 - a * c := by
    ring
  have hprod1 : 0 ≤ (a + 2 * c) * (c - a) := mul_nonneg (by omega) (by omega)
  have ha_bound : a ^ 2 + a * c ≤ 2 * c ^ 2 := by
    linarith
  -- z^2 + z*c ≥ 2*c^2 + 3*c + 1, with certificate (z - c - 1) * (z + 2*c + 1) ≥ 0
  have hexpand2 : (z - c - 1) * (z + 2 * c + 1) = z ^ 2 + z * c - 2 * c ^ 2 - 3 * c - 1 := by
    ring
  have hprod2 : 0 ≤ (z - c - 1) * (z + 2 * c + 1) := mul_nonneg (by omega) (by omega)
  have hstep : 2 * c ^ 2 + 3 * c + 1 ≤ z ^ 2 + z * c := by
    linarith
  -- rewrite the common norm using b = -(a + c)
  have hSa_ac : a ^ 2 + a * b + b ^ 2 = a ^ 2 + a * c + c ^ 2 := by
    rw [hb_eq]
    ring
  have hpos : 0 < z ^ 2 + z * c + c ^ 2 - (a ^ 2 + a * b + b ^ 2) := by
    rw [hSa_ac]
    linarith
  -- u*v = w^2 - (u^2+u*v+v^2) for both triples
  have hc_eq : c = -(a + b) := by omega
  have hc_sq : c ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by
    rw [hc_eq]
    ring
  have hab_eq : a * b = c ^ 2 - (a ^ 2 + a * b + b ^ 2) := by
    linarith
  have hz_eq : z = -(x + y) := by omega
  have hz_sq : z ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by
    rw [hz_eq]
    ring
  have hxy_eq : x * y = z ^ 2 - (x ^ 2 + x * y + y ^ 2) := by
    linarith
  have hxyz1 : x * y * z = (z ^ 2 - (x ^ 2 + x * y + y ^ 2)) * z :=
    congrArg (fun t : ℤ => t * z) hxy_eq
  have habc1 : a * b * c = (c ^ 2 - (a ^ 2 + a * b + b ^ 2)) * c :=
    congrArg (fun t : ℤ => t * c) hab_eq
  -- x*y*z - a*b*c = (z - c) * (z^2 + z*c + c^2 - S)
  have hdiff : x * y * z - a * b * c =
      (z - c) * (z ^ 2 + z * c + c ^ 2 - (a ^ 2 + a * b + b ^ 2)) := by
    rw [hxyz1, habc1, h7]
    ring
  have hprod_pos : 0 < (z - c) * (z ^ 2 + z * c + c ^ 2 - (a ^ 2 + a * b + b ^ 2)) :=
    mul_pos (by omega) hpos
  have hfinal : 0 < x * y * z - a * b * c := by
    rw [hdiff]
    exact hprod_pos
  linarith
