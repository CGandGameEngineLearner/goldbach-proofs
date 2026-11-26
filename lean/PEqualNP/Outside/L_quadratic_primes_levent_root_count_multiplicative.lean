import Mathlib

set_option linter.style.haveILetI false

/-! The prime case: `(roots 1 p).card` for a prime `p` is `1` for `p = 2`, `2` when `-1`
is a quadratic residue (`p % 4 = 1`), and `0` otherwise. -/
private theorem prime_root_card {p : ℕ} (hp : p.Prime) :
    ((Finset.range p).filter (fun r => p ∣ r^2+1)).card = if p=2 then 1 else if p%4=1 then 2 else 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    decide
  · haveI : NeZero p := ⟨hp.pos.ne'⟩
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hcard : ((Finset.range p).filter (fun r => p ∣ r^2+1)).card
        = (Finset.univ.filter (fun x : ZMod p => x^2 = -(1 : ZMod p))).card := by
      apply Finset.card_bij (fun (r : ℕ) (_ : r ∈ (Finset.range p).filter (fun r => p ∣ r^2+1)) => (r : ZMod p))
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        obtain ⟨hrlt, hrdiv⟩ := hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h2 : ((r^2 + 1 : ℕ) : ZMod p) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]; exact hrdiv
        push_cast at h2
        linear_combination h2
      · intro r1 hr1 r2 hr2 heq
        simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
        have h := ZMod.natCast_eq_natCast_iff' r1 r2 p
        rw [h] at heq
        rw [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at heq
        exact heq
      · intro x hx
        refine ⟨x.val, ?_, by rw [ZMod.natCast_zmod_val]⟩
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hx ⊢
        refine ⟨ZMod.val_lt x, ?_⟩
        have h2 : ((x.val^2 + 1 : ℕ) : ZMod p) = 0 := by
          push_cast
          rw [ZMod.natCast_zmod_val, hx]
          ring
        exact (ZMod.natCast_eq_zero_iff _ _).mp h2
    have key : (Finset.univ.filter (fun x : ZMod p => x^2 = -(1 : ZMod p))).card
        = ({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset.card := by
      rw [show ({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset
            = Finset.univ.filter (fun x : ZMod p => x^2 = ((-1:ℤ) : ZMod p)) from by ext x; simp]
      rw [show (((-1:ℤ) : ZMod p)) = -(1 : ZMod p) from by push_cast; ring]
    rw [ite_eq_right hp2, hcard, key]
    have hcs := legendreSym.card_sqrts p hp2 (-1)
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four p] at hcs
    rw [hp.mod_two_eq_one_iff_ne_two.mpr hp2] at hcs
    simp only [Nat.one_ne_zero, ite_false] at hcs
    split_ifs with h4
    · have h1 : (({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset.card : ℤ) = 2 := by
        rw [hcs]; simp [h4]
      omega
    · have h2 : (({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset.card : ℤ) = 0 := by
        rw [hcs]; simp [h4]
      omega

/-! Divisibility of `r ^ 2 + 1` only depends on `r` modulo the divisor. -/
private theorem dvd_mod_sq {n r : ℕ} (h : n ∣ r^2 + 1) : n ∣ (r % n)^2 + 1 := by
  rw [Nat.pow_two] at h ⊢
  have hc : r % n ≡ r [MOD n] := by simp [Nat.ModEq]
  have h0 : r * r + 1 ≡ 0 [MOD n] := Nat.modEq_zero_iff_dvd.mpr h
  exact Nat.modEq_zero_iff_dvd.mp (((hc.mul hc).add (Nat.ModEq.refl (n := n) 1)).trans h0)

/-! Existence part of the Chinese remainder theorem with an explicit bound. -/
private theorem exists_crt {q m u v : ℕ} (hq : 0 < q) (hm : 0 < m) (hc : q.Coprime m) :
    ∃ k, k < q * m ∧ k ≡ u [MOD q] ∧ k ≡ v [MOD m] :=
  ⟨(Nat.chineseRemainder hc u v : ℕ), Nat.chineseRemainder_lt_mul hc u v hq.ne' hm.ne',
    (Nat.chineseRemainder hc u v).prop.1, (Nat.chineseRemainder hc u v).prop.2⟩

/-! CRT multiplicativity of the root count for coprime moduli. -/
private theorem roots_mul_card {q m : ℕ} (hq : 0 < q) (hm : 0 < m) (hc : q.Coprime m) :
    ((Finset.range (q*m)).filter (fun r => q*m ∣ r^2+1)).card =
      ((Finset.range q).filter (fun r => q ∣ r^2+1)).card * ((Finset.range m).filter (fun r => m ∣ r^2+1)).card := by
  have hbij : ((Finset.range (q*m)).filter (fun r => q*m ∣ r^2+1)).card
      = (((Finset.range q).filter (fun r => q ∣ r^2+1)) ×ˢ ((Finset.range m).filter (fun r => m ∣ r^2+1))).card := by
    apply Finset.card_bij (fun (r : ℕ) (_ : r ∈ (Finset.range (q*m)).filter (fun r => q*m ∣ r^2+1)) => (r % q, r % m))
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hr ⊢
      obtain ⟨hlt, hdvd⟩ := hr
      exact ⟨⟨Nat.mod_lt _ hq, dvd_mod_sq ((dvd_mul_right q m).trans hdvd)⟩,
             ⟨Nat.mod_lt _ hm, dvd_mod_sq ((dvd_mul_left m q).trans hdvd)⟩⟩
    · intro r1 hr1 r2 hr2 heq
      simp only [Finset.mem_filter, Finset.mem_range, Prod.mk.injEq] at hr1 hr2 heq
      have e1 : r1 ≡ r2 [MOD q] := heq.1
      have e2 : r1 ≡ r2 [MOD m] := heq.2
      have h3 : r1 ≡ r2 [MOD q * m] := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨e1, e2⟩
      have h4 : r1 % (q*m) = r2 % (q*m) := h3
      rw [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at h4
      exact h4
    · rintro ⟨u, v⟩ ht
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at ht
      obtain ⟨⟨hu_lt, hu_dvd⟩, ⟨hv_lt, hv_dvd⟩⟩ := ht
      rw [Nat.pow_two] at hu_dvd hv_dvd
      obtain ⟨k, hk_lt, hku, hkv⟩ := exists_crt hq hm hc
      have hdvd' : q * m ∣ k ^ 2 + 1 := by
        rw [Nat.pow_two]
        have e1 : k * k + 1 ≡ 0 [MOD q] :=
          ((hku.mul hku).add (Nat.ModEq.refl (n := q) 1)).trans (Nat.modEq_zero_iff_dvd.mpr hu_dvd)
        have e2 : k * k + 1 ≡ 0 [MOD m] :=
          ((hkv.mul hkv).add (Nat.ModEq.refl (n := m) 1)).trans (Nat.modEq_zero_iff_dvd.mpr hv_dvd)
        have eand : k * k + 1 ≡ 0 [MOD q] ∧ k * k + 1 ≡ 0 [MOD m] := ⟨e1, e2⟩
        exact Nat.modEq_zero_iff_dvd.mp ((Nat.modEq_and_modEq_iff_modEq_mul hc).mp eand)
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt, hdvd'⟩,
        by rw [Nat.mod_eq_of_modEq hku hu_lt, Nat.mod_eq_of_modEq hkv hv_lt]⟩
  rw [hbij, Finset.card_product]

theorem PEqualNP.Outside.L_quadratic_primes_levent_root_count_multiplicative :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); ∀ q : ℕ, 0<q → Squarefree q → (roots 1 q).card = ∏ p ∈ q.primeFactors, (if p=2 then 1 else if p%4=1 then 2 else 0) := by
  dsimp only
  have main : ∀ n q : ℕ, q ≤ n → 0 < q → Squarefree q →
      ((Finset.range q).filter (fun r => q ∣ r^2+1)).card =
        ∏ p ∈ q.primeFactors, (if p=2 then 1 else if p%4=1 then 2 else 0) := by
    intro n
    induction n with
    | zero => intro q hqle h0 _; omega
    | succ n ih =>
      intro q hqle h0 hsq
      by_cases hq1 : q = 1
      · subst hq1
        simp only [Nat.primeFactors_one, Finset.prod_empty]
        decide
      · have h1lt : 1 < q := by omega
        obtain ⟨p, hp_mem⟩ := (Nat.nonempty_primeFactors.mpr h1lt).exists_mem
        obtain ⟨hp, hdvd, hqne0⟩ := Nat.mem_primeFactors.mp hp_mem
        obtain ⟨q', rfl⟩ : ∃ q', q = p * q' := ⟨q / p, (Nat.mul_div_cancel' hdvd).symm⟩
        rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
        · simp at h0
        · have hq'sq : Squarefree q' := hsq.squarefree_of_dvd (dvd_mul_left q' p)
          have hcop : p.Coprime q' := hp.coprime_iff_not_dvd.mpr (fun hcon =>
            absurd (Nat.mul_dvd_mul_left p hcon) ((Nat.squarefree_iff_prime_squarefree.mp hsq) p hp))
          have h1 : 2 * q' ≤ p * q' := Nat.mul_le_mul_right q' hp.two_le
          have hq'lt : q' < p * q' := lt_of_lt_of_le (by omega : q' < 2 * q') h1
          have hq'le : q' ≤ n := by omega
          have hdisj := hcop.disjoint_primeFactors
          rw [hcop.primeFactors_mul, Finset.prod_union hdisj, hp.primeFactors, Finset.prod_singleton,
            roots_mul_card hp.pos hq'pos hcop, prime_root_card hp, ih q' hq'le hq'pos hq'sq]
  intro q
  exact main q q (le_refl q)
