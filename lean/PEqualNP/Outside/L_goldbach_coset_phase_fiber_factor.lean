import Mathlib

namespace PEqualNP.Outside.CosetPhaseFiber

-- The complementary residue of the second index is unique.
private theorem residue_iff (n q i j : ℕ) (hq : 0 < q) :
    (i + j) % q = n % q ↔ j % q = (n + q - (i % q)) % q := by
  have hi : i % q ≤ n + q := by
    have := Nat.mod_lt i hq
    omega
  change Nat.ModEq q (i + j) n ↔ Nat.ModEq q j (n + q - i % q)
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add, Nat.cast_sub hi, ZMod.natCast_self, add_zero, ZMod.natCast_mod]
  rw [eq_sub_iff_add_eq, add_comm (i : ZMod q)]

-- Partition the admissible totals into the center and two disjoint progressions.
private theorem offset_sum (n q : ℕ) (hq : 0 < q) (f : ℕ → ℂ) :
    (∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q), f s) =
      f n + ∑ h ∈ Finset.Icc 1 (n / q), (f (n + h * q) + f (n - h * q)) := by
  let H := Finset.Icc 1 (n / q)
  let U := H.image (fun h => n + h * q)
  let D := H.image (fun h => n - h * q)
  have bounds {h : ℕ} (hh : h ∈ H) : 0 < h * q ∧ h * q ≤ n := by
    obtain ⟨hpos, hmax⟩ := Finset.mem_Icc.mp hh
    exact ⟨Nat.mul_pos hpos hq, (Nat.le_div_iff_mul_le hq).mp hmax⟩
  have up {s : ℕ} (hs : s ∈ U) : n < s := by
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hs
    have := (bounds hh).1
    omega
  have down {s : ℕ} (hs : s ∈ D) : s < n := by
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hs
    have := bounds hh
    omega
  have hsplit : (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q) =
      insert n (U ∪ D) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨hs, hres⟩
      have hmod : s ≡ n [MOD q] := hres
      rcases lt_trichotomy s n with hlt | heq | hgt
      · right; right
        obtain ⟨h, he⟩ := hmod.dvd'
        rw [Nat.mul_comm q h] at he
        refine Finset.mem_image.mpr ⟨h, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
        · by_contra! hh
          have : h = 0 := by omega
          simp [this] at he
          omega
        · apply (Nat.le_div_iff_mul_le hq).mpr
          omega
        · omega
      · exact Or.inl heq
      · right; left
        obtain ⟨h, he⟩ := hmod.symm.dvd'
        rw [Nat.mul_comm q h] at he
        refine Finset.mem_image.mpr ⟨h, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
        · by_contra! hh
          have : h = 0 := by omega
          simp [this] at he
          omega
        · apply (Nat.le_div_iff_mul_le hq).mpr
          omega
        · omega
    · rintro (rfl | hU | hD)
      · exact ⟨by omega, rfl⟩
      · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hU
        have := bounds hh
        exact ⟨by omega, by simp⟩
      · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hD
        have := bounds hh
        refine ⟨by omega, (Nat.modEq_iff_dvd' (Nat.sub_le n (h * q))).mpr ?_⟩
        exact ⟨h, by rw [Nat.mul_comm q h]; omega⟩
  have hndisj : n ∉ U ∪ D := by
    intro hn
    rcases Finset.mem_union.mp hn with hU | hD
    · exact (lt_irrefl n) (up hU)
    · exact (lt_irrefl n) (down hD)
  have hud : Disjoint U D := by
    apply Finset.disjoint_left.mpr
    intro s hU hD
    exact (lt_asymm (up hU)) (down hD)
  have hu : U.sum f = ∑ h ∈ H, f (n + h * q) := by
    apply Finset.sum_image
    intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_right hq (Nat.add_left_cancel hij)
  have hd : D.sum f = ∑ h ∈ H, f (n - h * q) := by
    apply Finset.sum_image
    intro i hi j hj hij
    change n - i * q = n - j * q at hij
    have := bounds hi
    have := bounds hj
    apply Nat.eq_of_mul_eq_mul_right hq
    omega
  rw [hsplit, Finset.sum_insert hndisj, Finset.sum_union hud, hu, hd, Finset.sum_add_distrib]

-- Reindex a pair first by its total, then by the residue of its first index.
private theorem fiber_sum (n q : ℕ) (hq : 0 < q) (v : ℕ → ℂ) :
    (∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q),
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ s ∧ s - k ≤ n), v k * v (s - k))
    = ∑ r ∈ Finset.range q,
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), v k) *
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = (n + q - r) % q), v k) := by
  have hres (i j : ℕ) := residue_iff n q i j hq
  let R := Finset.range (n + 1)
  let S := (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q)
  let F := fun r : ℕ => R.filter (fun k => k % q = r)
  let b := fun k : ℕ => v k * ∑ j ∈ F ((n + q - k % q) % q), v j
  calc
    (∑ s ∈ S, ∑ k ∈ R.filter (fun k => k ≤ s ∧ s - k ≤ n), v k * v (s - k))
        = ∑ k ∈ R, ∑ s ∈ S, if k ≤ s ∧ s - k ≤ n then v k * v (s - k) else 0 := by
          simp only [Finset.sum_filter]
          rw [Finset.sum_comm]
    _ = ∑ k ∈ R, ∑ j ∈ R.filter (fun j => (k + j) % q = n % q), v k * v j := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hkn : k ≤ n := by simpa [R] using hk
      rw [← Finset.sum_filter]
      apply Finset.sum_nbij' (fun s => s - k) (fun j => k + j)
      · intro s hs
        obtain ⟨hsS, hks, hsn⟩ := Finset.mem_filter.mp hs
        have hsmod := (Finset.mem_filter.mp hsS).2
        have heq : k + (s - k) = s := by omega
        exact Finset.mem_filter.mpr ⟨by simpa [R] using hsn, by simpa [heq] using hsmod⟩
      · intro j hj
        obtain ⟨hjR, hjmod⟩ := Finset.mem_filter.mp hj
        have hjn : j ≤ n := by simpa [R] using hjR
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjmod⟩, ?_⟩
        omega
      · intro s hs
        have hks := (Finset.mem_filter.mp hs).2.1
        omega
      · intro j _
        omega
      · intro s _
        rfl
    _ = ∑ k ∈ R, b k := by
      refine Finset.sum_congr rfl ?_
      intro k _
      simp only [b, F, Finset.mul_sum, hres]
    _ = ∑ r ∈ Finset.range q, ∑ k ∈ F r, b k :=
      (Finset.sum_fiberwise_of_maps_to (s := R) (t := Finset.range q)
        (g := fun k => k % q) (fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hq)) b).symm
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro r _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hkr : k % q = r := (Finset.mem_filter.mp hk).2
      simp only [b, hkr, F, R]

end PEqualNP.Outside.CosetPhaseFiber

theorem PEqualNP.Outside.L_goldbach_coset_phase_fiber_factor :
    let F := fun n q r : ℕ => (Finset.range (n + 1)).filter (fun k => k % q = r)
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let _A := fun n q r : ℕ => ∑ k ∈ F n q r, w k
    let j := fun n q r : ℕ => (n + q - r) % q
    let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n + 1)).filter
      (fun k => k ≤ s ∧ s - k ≤ n), w k * w (s - k)
    let Y := fun (n q : ℕ) (z : ℂ) => (B n n : ℂ) + ∑ h ∈ Finset.Icc 1 (n / q),
      ((B n (n + h * q) : ℂ) * z ^ h + (B n (n - h * q) : ℂ) * (z⁻¹) ^ h)
    ∀ (n q : ℕ) (u : ℂ), 0 < q → u ≠ 0 → u ^ n * Y n q (u ^ q) =
      ∑ r ∈ Finset.range q, (∑ k ∈ F n q r, (w k : ℂ) * u ^ k) *
        (∑ k ∈ F n q (j n q r), (w k : ℂ) * u ^ k) := by
  intro F w _A j B Y n q u hq hu
  let v (k : ℕ) : ℂ := (w k : ℂ) * u ^ k
  let c (s : ℕ) : ℂ := (B n s : ℂ) * u ^ s
  have coeff (s : ℕ) : c s = ∑ k ∈ (Finset.range (n + 1)).filter
      (fun k => k ≤ s ∧ s - k ≤ n), v k * v (s - k) := by
    dsimp only [c, B]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hks := (Finset.mem_filter.mp hk).2.1
    have hpow : u ^ s = u ^ k * u ^ (s - k) := by
      rw [← pow_add, show k + (s - k) = s by omega]
    dsimp only [v]
    rw [hpow]
    ring
  have upper (h : ℕ) : u ^ (n + h * q) = u ^ n * (u ^ q) ^ h := by
    rw [pow_add, ← pow_mul, Nat.mul_comm h q]
  have lower (h : ℕ) (hh : h ≤ n / q) : u ^ n * ((u ^ q)⁻¹) ^ h = u ^ (n - h * q) := by
    have hle := (Nat.le_div_iff_mul_le hq).mp hh
    have he : n - h * q + q * h = n := by rw [Nat.mul_comm q h]; omega
    have hpow : u ^ (n - h * q) * (u ^ q) ^ h = u ^ n := by rw [← pow_mul, ← pow_add, he]
    rw [inv_pow, ← hpow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hu)), mul_one]
  calc
    u ^ n * Y n q (u ^ q) = c n + ∑ h ∈ Finset.Icc 1 (n / q),
        (c (n + h * q) + c (n - h * q)) := by
      dsimp only [Y, c]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro h hh
        rw [mul_add, upper h, ← lower h (Finset.mem_Icc.mp hh).2]
        ring
    _ = ∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q), c s :=
      (PEqualNP.Outside.CosetPhaseFiber.offset_sum n q hq c).symm
    _ = ∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q),
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ s ∧ s - k ≤ n),
          v k * v (s - k) := Finset.sum_congr rfl (fun s _ => coeff s)
    _ = _ := PEqualNP.Outside.CosetPhaseFiber.fiber_sum n q hq v
