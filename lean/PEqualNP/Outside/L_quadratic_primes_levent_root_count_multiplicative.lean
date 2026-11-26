import Mathlib

private lemma roots_card_zmod (a n : ℕ) [NeZero n] :
    ((Finset.range n).filter (fun r => n ∣ r^2+a)).card
      = (Finset.univ.filter (fun u : ZMod n => u^2 + (a : ZMod n) = 0)).card := by
  apply Finset.card_bij (fun (r : ℕ) (_ : r ∈ (Finset.range n).filter (fun r => n ∣ r^2+a)) => (r : ZMod n))
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hr ⊢
    have h2 : ((r^2 + a : ℕ) : ZMod n) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact hr.2
    push_cast at h2
    linear_combination h2
  · intro r1 hr1 r2 hr2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
    have h := ZMod.natCast_eq_natCast_iff' r1 r2 n
    rw [h] at heq
    rw [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at heq
    exact heq
  · intro x hx
    refine ⟨x.val, ?_, by rw [ZMod.natCast_zmod_val]⟩
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨ZMod.val_lt x, ?_⟩
    have h2 : ((x.val^2 + a : ℕ) : ZMod n) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, hx]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h2

private lemma zmod_card_mul (a q m : ℕ) [NeZero q] [NeZero m] [NeZero (q*m)] (hc : q.Coprime m) :
    (Finset.univ.filter (fun u : ZMod (q*m) => u^2 + (a : ZMod (q*m)) = 0)).card
      = (Finset.univ.filter (fun u : ZMod q => u^2 + (a : ZMod q) = 0)).card
        * (Finset.univ.filter (fun u : ZMod m => u^2 + (a : ZMod m) = 0)).card := by
  let e : ZMod (q*m) ≃+* ZMod q × ZMod m := ZMod.chineseRemainder hc
  have hcongr : ∀ u : ZMod (q*m),
      (u^2 + (a : ZMod (q*m)) = 0)
        ↔ ((e u).1^2 + (a : ZMod q) = 0 ∧ (e u).2^2 + (a : ZMod m) = 0) := by
    intro u
    have hzero : (u^2 + (a : ZMod (q*m)) = 0) ↔ e (u^2 + (a : ZMod (q*m))) = 0 := by
      rw [← map_zero e, e.injective.eq_iff]
    rw [hzero, map_add, map_pow, map_natCast, Prod.ext_iff]
    simp
  have hbij : (Finset.univ.filter (fun u : ZMod (q*m) => u^2 + (a : ZMod (q*m)) = 0)).card
      = ((Finset.univ.filter (fun x : ZMod q => x^2 + (a : ZMod q) = 0))
          ×ˢ (Finset.univ.filter (fun y : ZMod m => y^2 + (a : ZMod m) = 0))).card := by
    apply Finset.card_bij (fun (u : ZMod (q*m)) (_ : u ∈ Finset.univ.filter (fun u : ZMod (q*m) => u^2 + (a : ZMod (q*m)) = 0)) => e u)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hu ⊢
      obtain ⟨h1, h2⟩ := (hcongr u).mp hu
      exact ⟨h1, h2⟩
    · intro u1 _ u2 _ h
      exact e.injective h
    · intro v hv
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨e.symm v, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcongr]
      simpa using hv
  rw [hbij, Finset.card_product]

private lemma roots_card_mul (a q m : ℕ) (hq : 0 < q) (hm : 0 < m) (hc : q.Coprime m) :
    ((Finset.range (q*m)).filter (fun r => q*m ∣ r^2+a)).card
      = ((Finset.range q).filter (fun r => q ∣ r^2+a)).card
        * ((Finset.range m).filter (fun r => m ∣ r^2+a)).card := by
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero (q*m) := ⟨(Nat.mul_pos hq hm).ne'⟩
  rw [roots_card_zmod a (q*m), roots_card_zmod a q, roots_card_zmod a m]
  exact zmod_card_mul a q m hc

private lemma roots_one_prime (p : ℕ) (hp : p.Prime) :
    ((Finset.range p).filter (fun r => p ∣ r^2+1)).card
      = if p=2 then 1 else if p%4=1 then 2 else 0 := by
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
    rw [if_neg hp2, hcard, key]
    have hcs := legendreSym.card_sqrts p hp2 (-1)
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four p] at hcs
    rw [hp.mod_two_eq_one_iff_ne_two.mpr hp2] at hcs
    simp only [Nat.one_ne_zero, if_false] at hcs
    split_ifs with h4
    · have h2 : (({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset.card : ℤ) = 2 := by
        rw [hcs]; simp [h4]
      omega
    · have h2 : (({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset.card : ℤ) = 0 := by
        rw [hcs]; simp [h4]
      omega

private lemma roots_card_prod (n : ℕ) (hn : Squarefree n) :
    ((Finset.range n).filter (fun r => n ∣ r^2+1)).card
      = ∏ p ∈ n.primeFactors, ((Finset.range p).filter (fun r => p ∣ r^2+1)).card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0
      exact absurd hn not_squarefree_zero
    rcases eq_or_ne n 1 with hn1 | hn1
    · subst hn1
      simp
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
    have hnk : n = p * (n / p) := (Nat.mul_div_cancel' hpdvd).symm
    have hkpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd) hp.pos
    have hklt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hp.one_lt
    have hsq : Squarefree (n / p) := Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpdvd) hn
    have hsquare := (Nat.squarefree_iff_prime_squarefree).mp hn
    have hnot : ¬ p ∣ n / p := by
      intro hdiv
      apply hsquare p hp
      rw [hnk]
      exact mul_dvd_mul_left p hdiv
    have hcop : p.Coprime (n / p) := hp.coprime_iff_not_dvd.mpr hnot
    have hpk : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
    have hpf : n.primeFactors = insert p (n / p).primeFactors := by
      conv_lhs => rw [← hpk]
      rw [Nat.Coprime.primeFactors_mul hcop, hp.primeFactors, Finset.singleton_union]
    have hmem : p ∉ (n / p).primeFactors := by
      intro h
      exact hnot (Nat.dvd_of_mem_primeFactors h)
    have hcard : ((Finset.range n).filter (fun r => n ∣ r^2+1)).card
        = ((Finset.range p).filter (fun r => p ∣ r^2+1)).card
          * ((Finset.range (n / p)).filter (fun r => n / p ∣ r^2+1)).card := by
      conv_lhs => rw [← hpk]
      exact roots_card_mul 1 p (n / p) hp.pos hkpos hcop
    rw [hcard, hpf, Finset.prod_insert hmem, ih (n / p) hklt hsq]

theorem PEqualNP.Outside.L_quadratic_primes_levent_root_count_multiplicative :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); ∀ q : ℕ, 0<q → Squarefree q → (roots 1 q).card = ∏ p ∈ q.primeFactors, (if p=2 then 1 else if p%4=1 then 2 else 0) := by
  dsimp only
  intro q hq hsq
  rw [roots_card_prod q hsq]
  exact Finset.prod_congr rfl (fun p hp => roots_one_prime p (Nat.prime_of_mem_primeFactors hp))
