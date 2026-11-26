import Mathlib

private theorem ld_projection (M : (ℕ → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ z, 0 ≤ M (z*z)) (S : Finset ℕ) (f : ℕ → ℝ)
    (g : ℕ → ℕ → ℝ) (a k : ℕ → ℝ)
    (hf : ∀ i ∈ S, M (g i * f) = a i)
    (hg : ∀ i ∈ S, ∀ j ∈ S, M (g i * g j) = if i=j then k i else 0)
    (hk : ∀ i ∈ S, k i ≠ 0) :
    ∑ i ∈ S, (a i)^2 / k i ≤ M (f*f) := by
  classical
  let c := fun i => a i / k i
  let y := ∑ i ∈ S, c i • g i
  have expn (z : ℕ → ℝ) : M (y*z) = ∑ i ∈ S, c i * M (g i*z) := by
    simp [y, Finset.sum_mul]
  have hy (j) (hj : j ∈ S) : M (y*g j) = a j := by
    rw [expn, Finset.sum_eq_single_of_mem j hj, hg j hj j hj, ite_eq_left rfl]
    · exact div_mul_cancel₀ _ (hk j hj)
    · intro i hi hij
      simp [hg i hi j hj, hij]
  have hr : M (y*(f-y)) = 0 := by
    rw [expn]
    apply Finset.sum_eq_zero
    intro i hi
    rw [mul_sub, map_sub, hf i hi, mul_comm (g i) y, hy i hi, sub_self, mul_zero]
  have hyf : M (y*f) = ∑ i ∈ S, (a i)^2 / k i := by
    rw [expn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hf i hi]
    dsimp [c]
    ring
  have h := hpos (f-y)
  have he : (f-y)*(f-y) = f*f-y*f-y*(f-y) := by ring
  rw [he, map_sub, map_sub, hyf, hr] at h
  linarith

private theorem ld_multiples {N d : ℕ} (hd : 0 < d) (hdiv : d ∣ N) (F : ℕ → ℝ) :
    (∑ t ∈ Finset.range N, if d ∣ t then F t else 0) =
      ∑ u ∈ Finset.range (N/d), F (d*u) := by
  obtain ⟨m, rfl⟩ := hdiv
  rw [Nat.mul_div_cancel_left _ hd, ← Finset.sum_filter]
  have hs : (Finset.range (d*m)).filter (fun t => d ∣ t) =
      (Finset.range m).image (fun u => d*u) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ht, u, rfl⟩
      exact ⟨u, (Nat.mul_lt_mul_left hd).mp ht, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(Nat.mul_lt_mul_left hd).mpr hu, ⟨u, rfl⟩⟩
  rw [hs, Finset.sum_image]
  intro x _ y _ h
  exact mul_left_cancel₀ hd.ne' h

theorem PEqualNP.Outside.L_goldbach_liouville_dilation_bessel :
    let L := fun n : ℕ => if n=0 then (0:ℝ) else (-1:ℝ)^n.primeFactorsList.length; let C := fun n : ℕ => (∑ t ∈ Finset.range n, L t * L (n-t))/(n:ℝ); ∀ N : ℕ, 0 < N → (∑ p ∈ N.divisors.filter Nat.Prime, (C (N/p)-C N)^2/((p:ℝ)-1)) ≤ ((N-1:ℕ):ℝ)/(N:ℝ)-(C N)^2 := by
  intro L C N hn
  classical
  let M : (ℕ → ℝ) →ₗ[ℝ] ℝ :=
    (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, (LinearMap.proj t : (ℕ → ℝ) →ₗ[ℝ] ℝ)
  have Mapp (z : ℕ → ℝ) : M z = (N:ℝ)⁻¹ * ∑ t ∈ Finset.range N, z t := by
    simp [M, LinearMap.sum_apply]
  have npos : (0 : ℝ) < N := by exact_mod_cast hn
  have Mpos (z : ℕ → ℝ) : 0 ≤ M (z*z) := by
    rw [Mapp]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => mul_self_nonneg (z t))
  have Mone : M 1 = 1 := by simp [Mapp, hn.ne']
  let H := fun (d t : ℕ) => if d ∣ t then (d:ℝ) else 0
  let F := fun t : ℕ => L t * L (N-t)
  have hm (d : ℕ) (hd : 0 < d) (hdiv : d ∣ N) (z : ℕ → ℝ) :
      M (H d * z) = (∑ u ∈ Finset.range (N/d), z (d*u)) / ((N/d:ℕ):ℝ) := by
    have hsum : (∑ t ∈ Finset.range N, (H d * z) t) =
        (∑ t ∈ Finset.range N, if d ∣ t then (d:ℝ) * z t else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : d ∣ t <;> simp [H,h]
    have he : (d:ℝ) * ((N/d:ℕ):ℝ) = N := by
      exact_mod_cast Nat.mul_div_cancel' hdiv
    have hq : ((N/d:ℕ):ℝ) ≠ 0 := by intro h; rw [h, mul_zero] at he; linarith
    rw [Mapp, hsum, ld_multiples hd hdiv, ← Finset.mul_sum]
    field_simp [npos.ne', hq]
    linear_combination (∑ u ∈ Finset.range (N/d), z (d*u)) * he
  have hH (d : ℕ) (hd : 0 < d) (hdiv : d ∣ N) : M (H d) = 1 := by
    have hq : 0 < N/d := Nat.div_pos (Nat.le_of_dvd hn hdiv) hd
    simpa [hq.ne'] using hm d hd hdiv 1
  have hL (p : ℕ) (hp : Nat.Prime p) (n : ℕ) : L (p*n) = -L n := by
    by_cases hz : n = 0
    · simp [hz, L]
    · have hlen := (Nat.perm_primeFactorsList_mul hp.ne_zero hz).length_eq
      simp only [Nat.primeFactorsList_prime hp, List.length_append, List.length_cons,
        List.length_nil, Nat.zero_add] at hlen
      simp [L, hz, hp.ne_zero, hlen, pow_add]
  have hMF : M F = C N := by simp [Mapp, F, C, div_eq_inv_mul]
  have hHF (p : ℕ) (hp : Nat.Prime p) (hd : p ∣ N) : M (H p*F) = C (N/p) := by
    rw [hm p hp.pos hd]
    change _ / _ = _ / _
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    have e : N - p*u = p*(N/p-u) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_div_cancel' hd]
    simp [F,e,hL p hp]
  have hHH (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
      (hdp : p ∣ N) (hdq : q ∣ N) : M (H p*H q) = if p=q then (p:ℝ) else 1 := by
    by_cases e : p=q
    · subst q
      have h : H p*H p = (p:ℝ) • H p := by
        ext t
        by_cases h : p ∣ t <;> simp [H,h]
      simp [h,hH p hp.pos hdp]
    · have cop := (Nat.coprime_primes hp hq).mpr e
      have h : H p*H q = H (p*q) := by
        ext t
        have e' : p*q ∣ t ↔ p ∣ t ∧ q ∣ t :=
          ⟨fun h => ⟨dvd_trans (dvd_mul_right p q) h, dvd_trans (dvd_mul_left q p) h⟩,
           fun ⟨h,k⟩ => cop.mul_dvd_of_dvd_of_dvd h k⟩
        by_cases a : p ∣ t <;> by_cases b : q ∣ t <;> simp [H,e',a,b]
      simp [h,e,hH _ (Nat.mul_pos hp.pos hq.pos) (cop.mul_dvd_of_dvd_of_dvd hdp hdq)]
  have hFF : M (F*F) = ((N-1:ℕ):ℝ)/(N:ℝ) := by
    have hL2 (t : ℕ) (ht : t ≠ 0) : L t * L t = 1 := by
      simp [L,ht,← mul_pow]
    have e : (∑ t ∈ Finset.range N, (F*F) t) =
        ∑ t ∈ Finset.range N, if t ≠ 0 then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases h : t = 0
      · simp [h,F,L]
      · have h' : N-t ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (Finset.mem_range.mp ht))
        simp only [Pi.mul_apply, F, ite_eq_left h]
        linear_combination (L (N-t) * L (N-t)) * (hL2 t h) + hL2 (N-t) h'
    rw [Mapp, e, ← Finset.sum_filter]
    simp [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_range.mpr hn), div_eq_inv_mul]
  let S := N.divisors.filter Nat.Prime
  let G := fun p => H p - 1
  let f := F - (C N) • (1 : ℕ → ℝ)
  have hmem (p) (hp : p ∈ S) : Nat.Prime p ∧ p ∣ N := by
    obtain ⟨h, h'⟩ := Finset.mem_filter.mp hp
    exact ⟨h', (Nat.mem_divisors.mp h).1⟩
  have hcov (p) (hp : p ∈ S) : M (G p*f) = C (N/p)-C N := by
    obtain ⟨h,d⟩ := hmem p hp
    have e : G p*f = H p*F - F - (C N) • H p + (C N) • 1 := by
      ext t; simp [G,f]; ring
    rw [e, map_add, map_sub, map_sub, map_smul, map_smul, Mone, hMF, hHF p h d, hH p h.pos d]
    simp
  have horth (p) (hp : p ∈ S) (q) (hq : q ∈ S) :
      M (G p*G q) = if p=q then (p:ℝ)-1 else 0 := by
    obtain ⟨h,d⟩ := hmem p hp
    obtain ⟨h',d'⟩ := hmem q hq
    have e : G p*G q = H p*H q-H p-H q+1 := by dsimp [G]; ring
    rw [e,map_add,map_sub,map_sub,hHH p q h h' d d',hH p h.pos d,hH q h'.pos d',Mone]
    split <;> ring
  have hv : M (f*f) = ((N-1:ℕ):ℝ)/(N:ℝ)-(C N)^2 := by
    have e : f*f = F*F-(2*C N) • F+(C N)^2 • 1 := by
      ext t; simp [f]; ring
    rw [e,map_add,map_sub,map_smul,map_smul,hFF,hMF,Mone]
    simp [smul_eq_mul]; ring
  rw [← hv]
  apply ld_projection M Mpos S f G (fun p => C (N/p)-C N) (fun p => (p:ℝ)-1) hcov horth
  intro p hp
  have h := (hmem p hp).1.one_lt
  have h' : (1:ℝ) < p := by exact_mod_cast h
  linarith
