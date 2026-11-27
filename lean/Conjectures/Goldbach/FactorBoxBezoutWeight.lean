import Mathlib

theorem Conjectures.Goldbach.FactorBoxBezoutWeight :
    ∀ (a b n l r u v : ℤ) (w : ℤ → ℤ → ℝ), 0 < a → 0 < b →
    let g : ℤ := Int.gcd a b
    let h := b / g
    let k := a / g
    let x := (n / g) * Int.gcdA a b
    let y := (n / g) * Int.gcdB a b
    let lo := max (-((x-l) / h)) (-((v-y) / k))
    let hi := min ((r-x) / h) ((y-u) / k)
    let box := ((Finset.Icc l r).product (Finset.Icc u v)).filter (fun z => a*z.1 + b*z.2 = n)
    (∑ z ∈ box, w z.1 z.2) = if g ∣ n then ∑ i ∈ Finset.Icc lo hi, w (x+h*i) (y-k*i) else 0 := by
  intro a b n l r u v w ha hb
  dsimp only
  set G : ℤ := (Int.gcd a b : ℤ) with hG
  set H : ℤ := b / G with hH
  set K : ℤ := a / G with hK
  set X : ℤ := (n / G) * Int.gcdA a b with hX
  set Y : ℤ := (n / G) * Int.gcdB a b with hY
  set LO : ℤ := max (-((X-l) / H)) (-((v-Y) / K)) with hLO
  set HI : ℤ := min ((r-X) / H) ((Y-u) / K) with hHI
  set BOX : Finset (ℤ × ℤ) :=
    ((Finset.Icc l r).product (Finset.Icc u v)).filter (fun z => a*z.1 + b*z.2 = n) with hBOX
  have hGpos : 0 < G := by
    rw [hG]
    have : 0 < Int.gcd a b := by
      rw [Int.gcd_def]
      exact Nat.gcd_pos_of_pos_left _ (by omega)
    exact_mod_cast this
  have hGne : G ≠ 0 := ne_of_gt hGpos
  have hGdvdA : G ∣ a := by rw [hG]; exact Int.gcd_dvd_left a b
  have hGdvdB : G ∣ b := by rw [hG]; exact Int.gcd_dvd_right a b
  have hGH : G * H = b := by rw [hH]; exact Int.mul_ediv_cancel' hGdvdB
  have hGK : G * K = a := by rw [hK]; exact Int.mul_ediv_cancel' hGdvdA
  have hHpos : 0 < H := by
    have hp : 0 < G * H := by rw [hGH]; exact hb
    rcases Int.mul_pos_iff.mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · omega
  have hKpos : 0 < K := by
    have hp : 0 < G * K := by rw [hGK]; exact ha
    rcases Int.mul_pos_iff.mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · omega
  have hHne : H ≠ 0 := ne_of_gt hHpos
  have hbez : a * Int.gcdA a b + b * Int.gcdB a b = G := by
    rw [hG]; exact (Int.gcd_eq_gcd_ab a b).symm
  have hcop : H.gcd K = 1 := by
    rw [hH, hK, hG]
    have h := Int.gcd_div_gcd_div_gcd (i := b) (j := a) (by simpa [Int.gcd_comm, hG] using hGpos)
    simpa [Int.gcd_comm, hG] using h
  have haH : a * H = b * K := by
    rw [← hGK, ← hGH]; ring
  have hb1 : ∀ i : ℤ, (-((X - l) / H) ≤ i) ↔ (l ≤ X + H * i) := by
    intro i
    have key : -i ≤ (X - l) / H ↔ (-i) * H ≤ X - l := Int.le_ediv_iff_mul_le hHpos
    constructor
    · intro h
      have h2 : -i ≤ (X - l) / H := by omega
      nlinarith [key.mp h2]
    · intro h
      have h2 : (-i) * H ≤ X - l := by nlinarith [h]
      have h3 := key.mpr h2
      omega
  have hb2 : ∀ i : ℤ, (i ≤ (r - X) / H) ↔ (X + H * i ≤ r) := by
    intro i
    have key : i ≤ (r - X) / H ↔ i * H ≤ r - X := Int.le_ediv_iff_mul_le hHpos
    constructor
    · intro h; nlinarith [key.mp h]
    · intro h; exact key.mpr (by nlinarith [h])
  have hb3 : ∀ i : ℤ, (-((v - Y) / K) ≤ i) ↔ (Y - K * i ≤ v) := by
    intro i
    have key : -i ≤ (v - Y) / K ↔ (-i) * K ≤ v - Y := Int.le_ediv_iff_mul_le hKpos
    constructor
    · intro h
      have h2 : -i ≤ (v - Y) / K := by omega
      nlinarith [key.mp h2]
    · intro h
      have h2 : (-i) * K ≤ v - Y := by nlinarith [h]
      have h3 := key.mpr h2
      omega
  have hb4 : ∀ i : ℤ, (i ≤ (Y - u) / K) ↔ (u ≤ Y - K * i) := by
    intro i
    have key : i ≤ (Y - u) / K ↔ i * K ≤ Y - u := Int.le_ediv_iff_mul_le hKpos
    constructor
    · intro h; nlinarith [key.mp h]
    · intro h; exact key.mpr (by nlinarith [h])
  have hmem : ∀ i : ℤ, i ∈ Finset.Icc LO HI ↔
      ((l ≤ X + H * i ∧ Y - K * i ≤ v) ∧ (X + H * i ≤ r ∧ u ≤ Y - K * i)) := by
    intro i
    rw [Finset.mem_Icc, hLO, hHI, max_le_iff, le_min_iff, hb1 i, hb2 i, hb3 i, hb4 i]
  by_cases hdiv : G ∣ n
  · rw [if_pos hdiv]
    have hXY : a * X + b * Y = n := by
      rw [hX, hY]
      have e : a * ((n / G) * Int.gcdA a b) + b * ((n / G) * Int.gcdB a b)
          = (n / G) * (a * Int.gcdA a b + b * Int.gcdB a b) := by ring
      rw [e, hbez]
      exact Int.ediv_mul_cancel hdiv
    have himg : BOX = (Finset.Icc LO HI).image (fun i => (X + H * i, Y - K * i)) := by
      ext z
      obtain ⟨p, q⟩ := z
      rw [hBOX]
      simp only [Finset.mem_filter, Finset.mem_image]
      simp
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
        have heq : a * (p - X) + b * (q - Y) = 0 := by nlinarith [hXY, h5]
        have heq2 : K * (p - X) + H * (q - Y) = 0 := by
          have hzero : G * (K * (p - X) + H * (q - Y)) = 0 := by
            have expand : G * (K * (p - X) + H * (q - Y)) = a * (p - X) + b * (q - Y) := by
              rw [← hGK, ← hGH]; ring
            rw [expand]; exact heq
          exact (mul_eq_zero.mp hzero).resolve_left hGne
        have hHK : H ∣ (p - X) * K := by
          refine ⟨Y - q, ?_⟩
          linear_combination heq2
        have hdvd : H ∣ (p - X) := Int.dvd_of_dvd_mul_left_of_gcd_one hHK hcop
        obtain ⟨i, hi⟩ := hdvd
        have hqi : q - Y = -K * i := by
          have h1 : K * (H * i) + H * (q - Y) = 0 := by rw [← hi]; exact heq2
          have hfac : H * (K * i + (q - Y)) = 0 := by linear_combination h1
          have := (mul_eq_zero.mp hfac).resolve_left hHne
          linarith
        have hpi : p = X + H * i := by linarith
        have hqi' : q = Y - K * i := by linarith
        refine ⟨i, ?_, ?_⟩
        · constructor
          · rw [hLO]
            exact max_le ((hb1 i).mpr (by linarith [hpi, h1])) ((hb3 i).mpr (by linarith [hqi', h4]))
          · rw [hHI]
            exact le_min ((hb2 i).mpr (by linarith [hpi, h2])) ((hb4 i).mpr (by linarith [hqi', h3]))
        · exact ⟨by linarith, by linarith⟩
      · rintro ⟨i, hi, heq1, heq2⟩
        rw [← heq1, ← heq2]
        rw [hLO] at hi
        rw [hHI] at hi
        have hlo := max_le_iff.mp hi.1
        have hhi := le_min_iff.mp hi.2
        refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
        · exact (hb1 i).mp hlo.1
        · exact (hb2 i).mp hhi.1
        · exact (hb4 i).mp hhi.2
        · exact (hb3 i).mp hlo.2
        · have e : a * (X + H * i) + b * (Y - K * i) = (a * X + b * Y) + i * (a * H - b * K) := by ring
          rw [e, haH, hXY]; ring
    rw [himg, Finset.sum_image]
    intro i _ j _ heq
    have h1 : X + H * i = X + H * j := (Prod.mk.injEq _ _ _ _ ▸ heq).1
    have h2 : H * i = H * j := by linarith
    exact mul_left_cancel₀ hHne h2
  · rw [if_neg hdiv]
    have hempty : BOX = ∅ := by
      ext z
      constructor
      · intro hz
        rw [hBOX, Finset.mem_filter] at hz
        obtain ⟨-, h3⟩ := hz
        have hdvd : G ∣ a * z.1 + b * z.2 := dvd_add (hGdvdA.mul_right z.1) (hGdvdB.mul_right z.2)
        rw [h3] at hdvd
        exact False.elim (hdiv hdvd)
      · intro hz
        simpa using hz
    rw [hempty]
    simp
