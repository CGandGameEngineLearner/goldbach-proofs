import Mathlib

/-- Remove shared shifted prime divisors by an exact disjoint sieve. -/

theorem Conjectures.Cuts.Cuta60732bfbe723d9ca8892663
    (h₁ : ∀ u v : ℕ, u ≠ v → u.primeFactorsList.length ≤ 2 → v.primeFactorsList.length ≤ 2 →
    (u.primeFactors ∩ v.primeFactors).card ≤ 1)
    (h₂ : by
  classical
  exact ∀ (U S : Finset ℕ) (I : ℕ → Finset ℕ),
    (∀ p ∈ U, I p ⊆ S ∧ (I p).card ≤ 1) →
    (U.filter (fun p => (I p).Nonempty)).card = ∑ r ∈ S, (U.filter (fun p => r ∈ I p)).card)
    (h₃ : by
  classical
  exact ∀ (n d : ℕ) (U : Finset ℕ), 0<d → U ⊆ Finset.range (n+1) →
    (U.filter (fun p => d ∣ p+2)).card = ((Finset.range ((n+2)/d+1)).filter (fun k => 2≤d*k ∧ d*k-2 ∈ U)).card)
    (h₄ : by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length≤2
    let U := fun (n R : ℕ) => (Finset.range (n+1)).filter (fun p => ch p ∧ ch (n-p) ∧ p ≠ n-p ∧ R ≤ (p+2).minFac)
    ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∃ T : ℕ, ∀ X ≥ T, ∃ R : ℕ, 0<R ∧
    (((Finset.Icc X (2*X)).filter (fun n => n % 6=4 ∧ (U n R).card ≤ Nat.log 2 (n+4)*((n+2)/R+1))).card:ℝ) ≤ C*(X:ℝ)^(1-δ))
    : (by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length≤2; ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∃ T : ℕ, ∀ X : ℕ, T≤X → (((Finset.Icc X (2*X)).filter (fun n : ℕ => n % 6=4 ∧ ¬ (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ (p+2).Coprime (q+2)))).card:ℝ)≤C*(X:ℝ)^(1-δ)) := by
  classical
  intro ch
  obtain ⟨δ,C,hδ,hδ',hC,T,hmass⟩ := h₄
  refine ⟨δ,C,hδ,hδ',hC,T,?_⟩
  intro X hX
  obtain ⟨R,hR,hcount⟩ := hmass X hX
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hcount
  intro n hn
  obtain ⟨hnX,hn6,hn⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hnX,hn6,?_⟩
  let U := (Finset.range (n+1)).filter (fun p => ch p ∧ ch (n-p) ∧ p ≠ n-p ∧ R ≤ (p+2).minFac)
  let I := fun p : ℕ => (p+2).primeFactors ∩ (n-p+2).primeFactors
  let B := U.filter (fun p => (I p).Nonempty)
  have ran : U ⊆ Finset.range (n+1) := Finset.filter_subset _ _
  have hi (p : ℕ) (hp : p ∈ U) : I p ⊆ (n+4).primeFactors ∧ (I p).card ≤ 1 := by
    obtain ⟨hr,hp',hq',hne,_⟩ := Finset.mem_filter.mp hp
    have hp0 := Finset.mem_range.mp hr
    constructor
    · intro r hr
      obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hr
      obtain ⟨hprime,hda,_⟩ := Nat.mem_primeFactors.mp ha
      have hdb := (Nat.mem_primeFactors.mp hb).2.1
      exact Nat.mem_primeFactors.mpr ⟨hprime,(show p+2+(n-p+2)=n+4 by omega) ▸ Nat.dvd_add hda hdb,by omega⟩
    · exact h₁ _ _ (by omega) hp'.2 hq'.2
  have bad : B.card = ∑ r ∈ (n+4).primeFactors, ((Finset.range ((n+2)/r+1)).filter (fun k => 2≤r*k ∧ r*k-2 ∈ U)).card := by
    change (U.filter (fun p => (I p).Nonempty)).card = _
    rw [h₂ U (n+4).primeFactors I hi]
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp hr
    have filterEq : U.filter (fun p => r ∈ I p) = U.filter (fun p => r∣p+2) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp,hrp⟩
        exact ⟨hp,(Nat.mem_primeFactors.mp (Finset.mem_inter.mp hrp).1).2.1⟩
      · rintro ⟨hp,hrp⟩
        have hp0 := Finset.mem_range.mp (ran hp)
        have hdb : r ∣ n-p+2 := (Nat.dvd_add_iff_right hrp).2 (by simpa only [show p+2+(n-p+2)=n+4 by omega] using hd)
        exact ⟨hp,Finset.mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hprime,hrp,by omega⟩,Nat.mem_primeFactors.mpr ⟨hprime,hdb,by omega⟩⟩⟩
    rw [filterEq]
    exact h₃ n r U hprime.pos ran
  have nix (p : ℕ) : (I p).Nonempty ↔ ¬ (p+2).Coprime (n-p+2) := by
    rw [Nat.Prime.not_coprime_iff_dvd]
    constructor
    · rintro ⟨r,hr⟩
      obtain ⟨a,b⟩ := Finset.mem_inter.mp hr
      exact ⟨r,(Nat.mem_primeFactors.mp a).1,(Nat.mem_primeFactors.mp a).2.1,(Nat.mem_primeFactors.mp b).2.1⟩
    · rintro ⟨r,hr,ha,hb⟩
      exact ⟨r,Finset.mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr,ha,by omega⟩,Nat.mem_primeFactors.mpr ⟨hr,hb,by omega⟩⟩⟩
  have hall : U ⊆ B := by
    intro p hp
    obtain ⟨hr,hp',hq',_⟩ := Finset.mem_filter.mp hp
    have hp0 := Finset.mem_range.mp hr
    exact Finset.mem_filter.mpr ⟨hp,(nix p).2 (fun hc => hn ⟨p,n-p,hp',hq',by omega,hc⟩)⟩
  have hc : (n+4).primeFactors.card ≤ Nat.log 2 (n+4) := by
    apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    calc
      2 ^ (n+4).primeFactors.card = ∏ _r ∈ (n+4).primeFactors, (2:ℕ) := by simp
      _ ≤ ∏ r ∈ (n+4).primeFactors, r := Finset.prod_le_prod (fun r hr => (Nat.mem_primeFactors.mp hr).1.two_le)
      _ ≤ n+4 := Nat.le_of_dvd (by omega) (n+4).prod_primeFactors_dvd
  change U.card ≤ _
  calc
    U.card ≤ B.card := Finset.card_le_card hall
    _ = _ := bad
    _ ≤ ∑ _r ∈ (n+4).primeFactors, ((n+2)/R+1) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hRr : R ≤ r
      · exact le_trans (by simpa using Finset.card_filter_le (s:=Finset.range ((n+2)/r+1)) (p:=fun k => 2≤r*k ∧ r*k-2 ∈ U)) (Nat.succ_le_succ (Nat.div_le_div_left hRr hR))
      · have he : ((Finset.range ((n+2)/r+1)).filter (fun k => 2≤r*k ∧ r*k-2 ∈ U)) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro k _ hk
          have rough := (Finset.mem_filter.mp hk.2).2.2.2.2
          have hk2 := hk.1
          have hd : r ∣ r*k-2+2 := (show r*k-2+2=r*k by omega) ▸ dvd_mul_right r k
          exact hRr (le_trans rough (Nat.minFac_le_of_dvd (Nat.mem_primeFactors.mp hr).1.two_le hd))
        simp [he]
    _ = _ := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hc
