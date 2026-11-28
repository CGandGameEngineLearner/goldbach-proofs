import Mathlib

private lemma mem_mid_symm {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3)) :
    n - u ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) ∧ 22 ≤ u ∧ 22 ≤ n - u ∧ u ≤ n := by
  rw [Finset.mem_Icc] at hu ⊢
  refine ⟨⟨by omega, by omega⟩, by omega, by omega, by omega⟩

private lemma coprime_sub_left {n u : ℕ} (hun : u ≤ n) (h : u.Coprime n) :
    (n - u).Coprime n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hd1 : Nat.gcd (n - u) n ∣ n - u := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd (n - u) n ∣ n := Nat.gcd_dvd_right _ _
  have hdu : Nat.gcd (n - u) n ∣ u := by
    simpa [Nat.sub_sub_self hun] using Nat.dvd_sub hd2 hd1
  exact Nat.dvd_one.mp (h.gcd_eq_one ▸ Nat.dvd_gcd hdu hd2)

private lemma minFac_pair_eq {n p m : ℕ} (hp : p.Prime) (hu : 2 ≤ p * m)
    (hnu : 2 ≤ n - p * m)
    (hno : ∀ q ∈ Finset.range p, q.Prime → ¬ q ∣ m * (n - p * m)) :
    (p * m * (n - p * m)).minFac = p := by
  have hpos : 1 < p * m * (n - p * m) := by nlinarith
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hp.two_le ⟨m * (n - p * m), by ring⟩
  · by_contra hlt
    push_neg at hlt
    set q := (p * m * (n - p * m)).minFac
    have hq : q.Prime := Nat.minFac_prime (by omega)
    have hqd : q ∣ p * (m * (n - p * m)) := by
      simpa [mul_assoc] using Nat.minFac_dvd (p * m * (n - p * m))
    rcases hq.dvd_mul.mp hqd with hqp | hqm
    · rcases (Nat.dvd_prime hp).mp hqp with hq1 | rfl
      · exact hq.ne_one hq1
      · exact Nat.lt_irrefl q hlt
    · exact hno q (Finset.mem_range.mpr hlt) hq hqm

private lemma card_eq_two_mul_pairs {n z0 z1 : ℕ} (hn : 64 ≤ n) :
    ({u ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) |
        u.Coprime n ∧ z0 < (u * (n - u)).minFac ∧ (u * (n - u)).minFac ≤ z1}).card =
      2 * ({pm ∈ (Finset.Ioc z0 z1).product (Finset.range (n + 1)) |
        Nat.Prime pm.1 ∧ pm.1 * pm.2 ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) ∧
          (pm.1 * pm.2).Coprime n ∧
          ∀ q ∈ Finset.range pm.1, Nat.Prime q → ¬ q ∣ pm.2 * (n - pm.1 * pm.2)}).card := by
  set S := {u ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) |
    u.Coprime n ∧ z0 < (u * (n - u)).minFac ∧ (u * (n - u)).minFac ≤ z1}
  set P := {pm ∈ (Finset.Ioc z0 z1).product (Finset.range (n + 1)) |
    Nat.Prime pm.1 ∧ pm.1 * pm.2 ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) ∧
      (pm.1 * pm.2).Coprime n ∧
      ∀ q ∈ Finset.range pm.1, Nat.Prime q → ¬ q ∣ pm.2 * (n - pm.1 * pm.2)}
  set A := S.filter (fun u => (u * (n - u)).minFac ∣ u)
  set B := S.filter (fun u => ¬ ((u * (n - u)).minFac ∣ u))
  have hsplit : S.card = A.card + B.card :=
    (Finset.card_filter_add_card_filter_not (s := S)
      (p := fun u => (u * (n - u)).minFac ∣ u)).symm
  have hA : A.card = P.card := by
    refine Finset.card_bij'
      (fun u _ => ((u * (n - u)).minFac, u / (u * (n - u)).minFac))
      (fun pm _ => pm.1 * pm.2) ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨huS, hdvd⟩ := Finset.mem_filter.mp hu
      obtain ⟨hu1, hcop, hz0, hz1⟩ := Finset.mem_filter.mp huS
      obtain ⟨_, hu22, hnu22, hun⟩ := mem_mid_symm hn hu1
      set p := (u * (n - u)).minFac
      have hp : p.Prime := Nat.minFac_prime (by nlinarith)
      have hmul : p * (u / p) = u := Nat.mul_div_cancel' hdvd
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨hz0, hz1⟩,
        Finset.mem_range.mpr (by have := Nat.div_le_self u p; omega)⟩,
        hp, ?_, ?_, ?_⟩
      · rwa [hmul]
      · rwa [hmul]
      · intro q hq hpq hqd
        have hq' : q < p := Finset.mem_range.mp hq
        have hfac : p * ((u / p) * (n - p * (u / p))) = u * (n - u) := by
          rw [hmul]
        have hd : q ∣ u * (n - u) := by
          rw [← hfac]
          exact dvd_mul_of_dvd_right hqd p
        exact absurd (Nat.minFac_le_of_dvd hpq.two_le hd) (not_le_of_gt hq')
    · intro pm hpm
      obtain ⟨hprod, hp, hu1, hcop, hno⟩ := Finset.mem_filter.mp hpm
      obtain ⟨hz, _⟩ := Finset.mem_product.mp hprod
      obtain ⟨hz0, hz1⟩ := Finset.mem_Ioc.mp hz
      obtain ⟨_, hu22, hnu22, _⟩ := mem_mid_symm hn hu1
      have hmin := minFac_pair_eq hp (by omega) (by omega) hno
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hu1, hcop, ?_, ?_⟩, ?_⟩
      · rwa [hmin]
      · rwa [hmin]
      · rw [hmin]; exact dvd_mul_right pm.1 pm.2
    · intro u hu
      obtain ⟨_, hdvd⟩ := Finset.mem_filter.mp hu
      exact Nat.mul_div_cancel' hdvd
    · intro pm hpm
      obtain ⟨_, hp, hu1, _, hno⟩ := Finset.mem_filter.mp hpm
      obtain ⟨_, hu22, hnu22, _⟩ := mem_mid_symm hn hu1
      have hmin := minFac_pair_eq hp (by omega) (by omega) hno
      ext
      · exact hmin
      · dsimp only
        rw [hmin]
        exact Nat.mul_div_cancel_left pm.2 hp.pos
  have hB : B.card = P.card := by
    refine Finset.card_bij'
      (fun u _ => ((u * (n - u)).minFac, (n - u) / (u * (n - u)).minFac))
      (fun pm _ => n - pm.1 * pm.2) ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨huS, hndvd⟩ := Finset.mem_filter.mp hu
      obtain ⟨hu1, hcop, hz0, hz1⟩ := Finset.mem_filter.mp huS
      obtain ⟨hnu1, hu22, hnu22, hun⟩ := mem_mid_symm hn hu1
      set p := (u * (n - u)).minFac
      have hp : p.Prime := Nat.minFac_prime (by nlinarith)
      have hpdvd : p ∣ u * (n - u) := Nat.minFac_dvd _
      have hdvd : p ∣ n - u := (hp.dvd_mul.mp hpdvd).resolve_left hndvd
      have hmul : p * ((n - u) / p) = n - u := Nat.mul_div_cancel' hdvd
      have hsub : n - p * ((n - u) / p) = u := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨hz0, hz1⟩,
        Finset.mem_range.mpr (by have := Nat.div_le_self (n - u) p; omega)⟩,
        hp, ?_, ?_, ?_⟩
      · rwa [hmul]
      · rw [hmul]; exact coprime_sub_left hun hcop
      · intro q hq hpq hqd
        have hq' : q < p := Finset.mem_range.mp hq
        have hfac : p * (((n - u) / p) * (n - p * ((n - u) / p))) = u * (n - u) := by
          rw [hsub, ← mul_assoc, hmul, mul_comm]
        have hd : q ∣ u * (n - u) := by
          rw [← hfac]
          exact dvd_mul_of_dvd_right hqd p
        exact absurd (Nat.minFac_le_of_dvd hpq.two_le hd) (not_le_of_gt hq')
    · intro pm hpm
      obtain ⟨hprod, hp, hv1, hcop, hno⟩ := Finset.mem_filter.mp hpm
      obtain ⟨hz, _⟩ := Finset.mem_product.mp hprod
      obtain ⟨hz0, hz1⟩ := Finset.mem_Ioc.mp hz
      obtain ⟨hu1, hv22, hnv22, hvn⟩ := mem_mid_symm hn hv1
      have hmin_v := minFac_pair_eq hp (by omega) (by omega) hno
      have hsub : n - (n - pm.1 * pm.2) = pm.1 * pm.2 := by omega
      have hmin : ((n - pm.1 * pm.2) * (n - (n - pm.1 * pm.2))).minFac = pm.1 := by
        rw [hsub, mul_comm]; exact hmin_v
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hu1, coprime_sub_left hvn hcop, ?_, ?_⟩, ?_⟩
      · rwa [hmin]
      · rwa [hmin]
      · rw [hmin]
        intro hpu
        have hpn : pm.1 ∣ n := by
          have hadd : (n - pm.1 * pm.2) + pm.1 * pm.2 = n := by omega
          rw [← hadd]
          exact Nat.dvd_add hpu (dvd_mul_right pm.1 pm.2)
        have hp1 : pm.1 ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_mul_right pm.1 pm.2) hpn
        exact hp.ne_one (Nat.dvd_one.mp hp1)
    · intro u hu
      obtain ⟨huS, hndvd⟩ := Finset.mem_filter.mp hu
      obtain ⟨hu1, _⟩ := Finset.mem_filter.mp huS
      obtain ⟨_, hu22, hnu22, hun⟩ := mem_mid_symm hn hu1
      set p := (u * (n - u)).minFac
      have hp : p.Prime := Nat.minFac_prime (by nlinarith)
      have hdvd : p ∣ n - u := (hp.dvd_mul.mp (Nat.minFac_dvd _)).resolve_left hndvd
      rw [Nat.mul_div_cancel' hdvd]
      omega
    · intro pm hpm
      obtain ⟨_, hp, hv1, _, hno⟩ := Finset.mem_filter.mp hpm
      obtain ⟨_, hv22, hnv22, hvn⟩ := mem_mid_symm hn hv1
      have hmin_v := minFac_pair_eq hp (by omega) (by omega) hno
      have hsub : n - (n - pm.1 * pm.2) = pm.1 * pm.2 := by omega
      have hmin : ((n - pm.1 * pm.2) * (n - (n - pm.1 * pm.2))).minFac = pm.1 := by
        rw [hsub, mul_comm]; exact hmin_v
      ext
      · exact hmin
      · dsimp only
        rw [hmin, hsub]
        exact Nat.mul_div_cancel_left pm.2 hp.pos
  omega

theorem Conjectures.Cuts.Taskbc45812d7a3b53e078e42d66 : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ → ℕ → Finset (ℕ × ℕ) := fun (x2 x3 x4 : ℕ) =>   {x5 ∈ (Finset.Ioc x3 x4).product (Finset.range (x2 + (1 : ℕ))) |     have x6 : ℕ := x5.1;     have x7 : ℕ := x5.2;     Nat.Prime x6 ∧ x6 * x7 ∈ x1 x2 ∧ (x6 * x7).Coprime x2 ∧ ∀ x8 ∈ Finset.range x6, Nat.Prime x8 → ¬x8 ∣ x7 * (x2 - x6 * x7)}; have x3 : ℕ → ℕ → ℕ → Finset ℕ := fun (x3 x4 x5 : ℕ) => {x6 ∈ x1 x3 | x6.Coprime x3 ∧ x4 < (x6 * (x3 - x6)).minFac ∧ (x6 * (x3 - x6)).minFac ≤ x5}; ∀ (x4 x5 x6 : ℕ), (64 : ℕ) ≤ x4 → (x3 x4 x5 x6).card = (2 : ℕ) * (x2 x4 x5 x6).card) := by
  dsimp only
  intro n z0 z1 hn
  exact card_eq_two_mul_pairs hn
