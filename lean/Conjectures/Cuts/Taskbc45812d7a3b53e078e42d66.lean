import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.ByContra

private def win (n : ℕ) := Finset.Icc ((n+2)/3) (2*n/3)
private def fac (n u : ℕ) := (u*(n-u)).minFac
private def hits (n l h : ℕ) := (win n).filter (fun u => u.Coprime n ∧ l < fac n u ∧ fac n u ≤ h)
private def lefts (n l h : ℕ) := (hits n l h).filter (fun u => fac n u ∣ u)
private def pairs (n l h : ℕ) := ((Finset.Ioc l h).product (Finset.range (n+1))).filter
  (fun v => v.1.Prime ∧ v.1*v.2 ∈ win n ∧ (v.1*v.2).Coprime n ∧
    ∀ q ∈ Finset.range v.1, q.Prime → ¬ q ∣ v.2*(n-v.1*v.2))

private lemma farey_reflect (n l h : ℕ) (hn : 64 ≤ n) :
    (hits n l h).card = 2 * (lefts n l h).card := by
  let R := (hits n l h).filter (fun u => ¬ fac n u ∣ u)
  have hflip (u : ℕ) (hu : u ∈ hits n l h) :
      n-u ∈ hits n l h ∧ (fac n (n-u) ∣ n-u ↔ ¬ fac n u ∣ u) ∧ n-(n-u)=u := by
    obtain ⟨hw,hcop,hlo,hhi⟩ := Finset.mem_filter.mp hu
    obtain ⟨hw₁,hw₂⟩ := Finset.mem_Icc.mp hw
    have hun : u ≤ n := by omega
    have hinv : n-(n-u)=u := by omega
    have hf : fac n (n-u) = fac n u := by simp only [fac, hinv, Nat.mul_comm (n-u) u]
    have hp : (fac n u).Prime := by
      apply Nat.minFac_prime
      have hl : 2 ≤ u := by omega
      have hr : 2 ≤ n-u := by omega
      exact (ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2*2) (Nat.mul_le_mul hl hr)))
    have hexcl (h₁ : fac n u ∣ u) (h₂ : fac n u ∣ n-u) : False := by
      have hco := (Nat.coprime_sub_self_right hun).mpr hcop
      exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨_, hp, h₁, h₂⟩) hco
    have hd : fac n u ∣ u*(n-u) := Nat.minFac_dvd _
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
      (Nat.coprime_self_sub_left hun).mpr hcop, hf ▸ hlo, hf ▸ hhi⟩, ?_, hinv⟩
    rw [hf]
    exact ⟨fun hb ha => hexcl ha hb, fun ha => (hp.dvd_mul.mp hd).resolve_left ha⟩
  have heq : (lefts n l h).card = R.card := by
    apply Finset.card_bij' (fun u _ => n-u) (fun u _ => n-u)
    · intro u hu
      obtain ⟨hin,hl⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨(hflip u hin).1, fun hr => (hflip u hin).2.1.mp hr hl⟩
    · intro u hu
      obtain ⟨hin,hr⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨(hflip u hin).1, (hflip u hin).2.1.mpr hr⟩
    · intro u hu
      exact (hflip u (Finset.mem_filter.mp hu).1).2.2
    · intro u hu
      exact (hflip u (Finset.mem_filter.mp hu).1).2.2
  have hsum : (lefts n l h).card + R.card = (hits n l h).card :=
    Finset.card_filter_add_card_filter_not _
  omega

private lemma left_to_pair (n l h u : ℕ) (hn : 64 ≤ n) (hu : u ∈ lefts n l h) :
    (fac n u, u / fac n u) ∈ pairs n l h ∧ fac n u * (u / fac n u) = u := by
  obtain ⟨hmem, hdvd⟩ := Finset.mem_filter.mp hu
  obtain ⟨hwin, hcop, hlo, hhi⟩ := Finset.mem_filter.mp hmem
  have hbounds := Finset.mem_Icc.mp (show u ∈ win n from hwin)
  change (n+2)/3 ≤ u ∧ u ≤ 2*n/3 at hbounds
  have hmul : fac n u * (u / fac n u) = u := Nat.mul_div_cancel' hdvd
  have hu2 : 2 ≤ u := by omega
  have hnu : 1 ≤ n-u := by omega
  have hprime : (fac n u).Prime := Nat.minFac_prime (by
    have hle := Nat.mul_le_mul hu2 hnu
    omega)
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo,hhi⟩,
    Finset.mem_range.mpr ((Nat.div_le_self _ _).trans_lt (by omega))⟩, ?_⟩, hmul⟩
  dsimp only [Prod.fst, Prod.snd]
  rw [hmul]
  refine ⟨hprime, hwin, hcop, ?_⟩
  intro q hq hqprime hqdiv
  have hfull : q ∣ u * (n-u) := by
    have hm := dvd_mul_of_dvd_right hqdiv (fac n u)
    rwa [← Nat.mul_assoc, hmul] at hm
  exact (Finset.mem_range.mp hq).not_ge (Nat.minFac_le_of_dvd hqprime.two_le hfull)

private lemma pair_to_left (n l h p k : ℕ) (_hn : 64 ≤ n) (hv : (p,k) ∈ pairs n l h) :
    p*k ∈ lefts n l h ∧ fac n (p*k) = p := by
  obtain ⟨hprod, hp, hw, hcop, hsmall⟩ := Finset.mem_filter.mp hv
  obtain ⟨hIoc, _⟩ := Finset.mem_product.mp hprod
  obtain ⟨hlp, hph⟩ := Finset.mem_Ioc.mp hIoc
  have hd : p ∣ p * k * (n-p*k) := ⟨k*(n-p*k), Nat.mul_assoc ..⟩
  have hne : p*k*(n-p*k) ≠ 1 := fun he => hp.not_dvd_one (he ▸ hd)
  have hf : fac n (p*k) = p := by
    unfold fac
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le hd)
    apply (Nat.le_minFac.mpr ?_).resolve_left hne
    intro q hq hqd
    by_contra! hqp
    rw [Nat.mul_assoc] at hqd
    rcases hq.dvd_mul.mp hqd with hdiv | hdiv
    · exact hqp.ne ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdiv)
    · exact hsmall q (Finset.mem_range.mpr hqp) hq hdiv
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw, hcop, ?_⟩, ?_⟩, hf⟩
  · simpa only [hf] using And.intro hlp hph
  · rw [hf]
    exact dvd_mul_right p k

private lemma count_one_side (n l h : ℕ)
    (encode : ∀ u ∈ lefts n l h,
      (fac n u, u / fac n u) ∈ pairs n l h ∧ fac n u * (u / fac n u) = u)
    (decode : ∀ p k, (p,k) ∈ pairs n l h →
      p*k ∈ lefts n l h ∧ fac n (p*k) = p) :
    (lefts n l h).card = (pairs n l h).card := by
  apply Finset.card_nbij' (fun u => (fac n u, u / fac n u)) (fun v => v.1*v.2)
  · intro u hu
    exact (encode u hu).1
  · intro v hv
    exact (decode v.1 v.2 hv).1
  · intro u hu
    exact (encode u hu).2
  · rintro ⟨p,k⟩ hv
    obtain ⟨_, hp⟩ := decode p k hv
    have pp := (Finset.mem_filter.mp (show (p,k) ∈ pairs n l h from hv)).2.1
    change (fac n (p*k), p*k / fac n (p*k)) = (p,k)
    rw [hp, Nat.mul_div_cancel_left _ pp.pos]

theorem Conjectures.Cuts.Taskbc45812d7a3b53e078e42d66 : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ → ℕ → Finset (ℕ × ℕ) := fun (x2 x3 x4 : ℕ) =>   {x5 ∈ (Finset.Ioc x3 x4).product (Finset.range (x2 + (1 : ℕ))) |     have x6 : ℕ := x5.1;     have x7 : ℕ := x5.2;     Nat.Prime x6 ∧ x6 * x7 ∈ x1 x2 ∧ (x6 * x7).Coprime x2 ∧ ∀ x8 ∈ Finset.range x6, Nat.Prime x8 → ¬x8 ∣ x7 * (x2 - x6 * x7)}; have x3 : ℕ → ℕ → ℕ → Finset ℕ := fun (x3 x4 x5 : ℕ) => {x6 ∈ x1 x3 | x6.Coprime x3 ∧ x4 < (x6 * (x3 - x6)).minFac ∧ (x6 * (x3 - x6)).minFac ≤ x5}; ∀ (x4 x5 x6 : ℕ), (64 : ℕ) ≤ x4 → (x3 x4 x5 x6).card = (2 : ℕ) * (x2 x4 x5 x6).card) := by
  intro I P S n l h hn
  change (hits n l h).card = 2 * (pairs n l h).card
  rw [farey_reflect n l h hn, count_one_side n l h (fun u hu => left_to_pair n l h u hn hu) (fun p k hv => pair_to_left n l h p k hn hv)]
