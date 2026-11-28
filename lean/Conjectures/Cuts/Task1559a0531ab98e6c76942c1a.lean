import Mathlib


private theorem sparseRadixTrunc : (∀ (b k n : ℕ), 2 ≤ b → (∑ i : Fin k, ((n/b^(i:ℕ)) % b)*b^(i:ℕ)) = n % b^k) := by
  intro b k n hb
  have tel (j : ℕ) : (∑ i : Fin j, ((n/b^(i:ℕ)) % b)*b^(i:ℕ)) + (n/b^j)*b^j = n := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, pow_succ]
      rw [← Nat.div_div_eq_div_mul]
      have hd := congrArg (fun z : ℕ => z*b^j) (Nat.mod_add_div (n/b^j) b)
      nlinarith only [ih,hd]
  have ht := tel k
  have hm := Nat.mod_add_div n (b^k)
  rw [Nat.mul_comm (b^k)] at hm
  omega


private theorem sparseRadixWord : (∀ (b k : ℕ), 2 ≤ b → ∀ w : Fin k → ℕ, (∀ i, w i < b) →
    let n := ∑ i : Fin k, w i*b^(i:ℕ)
    n < b^k ∧ ∀ i : Fin k, (n/b^(i:ℕ)) % b = w i) := by
  intro b k hb
  induction k with
  | zero =>
    intro w _
    simp
  | succ k ih =>
    intro w hw
    let a := ∑ i : Fin k, w i.succ * b^(i:ℕ)
    have htail := ih (fun i => w i.succ) (fun i => hw i.succ)
    change a < b^k ∧ ∀ i : Fin k, (a/b^(i:ℕ)) % b = w i.succ at htail
    have splitSum : (∑ i : Fin (k+1), w i*b^(i:ℕ)) = w 0 + b*a := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      dsimp only [a]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by ring)
    dsimp only
    rw [splitSum]
    have h0 := hw 0
    have hpos : 0 < b := by omega
    have hdiv : (w 0 + b*a)/b = a := by simp [Nat.add_mul_div_left, hpos, Nat.div_eq_of_lt h0]
    constructor
    · rw [pow_succ']
      calc
        w 0+b*a < b+b*a := Nat.add_lt_add_right h0 _
        _ = b*(a+1) := by ring
        _ ≤ b*b^k := Nat.mul_le_mul_left _ htail.1
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Nat.add_mod, Nat.mod_eq_of_lt h0]
      · rw [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
        exact htail.2 j

theorem Conjectures.Cuts.Task1559a0531ab98e6c76942c1a : (by
  classical
  exact ∀ b k j : ℕ, 2 ≤ b → ∀ R : Finset ℕ,
    let S := (Finset.range (b^k)).filter (fun n : ℕ => (∀ i < k, (n/b^i) % b ≤ 1) ∧ ((Finset.range k).filter (fun i => (n/b^i) % b=1)).card=j)
    let B := (Finset.range k).powersetCard j
    let v := fun s : Finset ℕ => ∑ i ∈ s, b^i
    (S.filter (fun n => n ∈ R)).card = (B.filter (fun s => v s ∈ R)).card ∧ S.card = k.choose j) := by
  classical
  intro b k j hb R S B v
  let bits (n : ℕ) := (Finset.range k).filter (fun i => n/b^i % b = 1)
  have code (s : Finset ℕ) (hs : s ⊆ Finset.range k) :
      (∑ i : Fin k, (if (i:ℕ) ∈ s then 1 else 0)*b^(i:ℕ)) = v s := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (if i ∈ s then 1 else 0)*b^i)]
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
    have he : (Finset.range k).filter (fun i => i ∈ s) = s := by ext i; simp only [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨hs h,h⟩⟩
    rw [he]
  have decode (s : Finset ℕ) (hs : s ⊆ Finset.range k) :
      v s < b^k ∧ ∀ i : Fin k, v s / b^(i:ℕ) % b = if (i:ℕ) ∈ s then 1 else 0 := by
    have hh := sparseRadixWord b k hb (fun i => if (i:ℕ) ∈ s then 1 else 0)
      (fun i => by split <;> omega)
    change (∑ i : Fin k, (if (i:ℕ) ∈ s then 1 else 0)*b^(i:ℕ)) < _ ∧ _ at hh
    simpa only [code s hs] using hh
  have inverse (s : Finset ℕ) (hs : s ⊆ Finset.range k) : bits (v s) = s := by
    ext i
    by_cases hi : i < k
    · have hd := (decode s hs).2 ⟨i,hi⟩
      change v s / b^i % b = (if i ∈ s then 1 else 0) at hd
      simp [bits,hi,hd]
    · have hn : i ∉ s := fun h => hi (Finset.mem_range.mp (hs h))
      simp [bits,hi,hn]
  have inj : Set.InjOn v B := by
    intro s hs t ht eq
    exact (inverse s (Finset.mem_powersetCard.mp hs).1).symm.trans ((congrArg bits eq).trans (inverse t (Finset.mem_powersetCard.mp ht).1))
  have image : B.image v = S := by
    ext n
    constructor
    · rintro hn
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hs
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (decode s hsub).1, ?_, ?_⟩
      · intro i hi
        have hd := (decode s hsub).2 ⟨i,hi⟩
        change v s / b^i % b = (if i ∈ s then 1 else 0) at hd
        rw [hd]; split <;> decide
      · exact (congrArg Finset.card (inverse s hsub)).trans hcard
    · intro hn
      obtain ⟨hr,hd,hcard⟩ := Finset.mem_filter.mp hn
      have hs : bits n ⊆ Finset.range k := Finset.filter_subset _ _
      refine Finset.mem_image.mpr ⟨bits n, Finset.mem_powersetCard.mpr ⟨hs,hcard⟩,?_⟩
      rw [← code _ hs]
      calc
        _ = ∑ i : Fin k, (n/b^(i:ℕ) % b)*b^(i:ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          have le := hd i i.isLt
          have eq : (if (i:ℕ) ∈ bits n then 1 else 0) = (n/b^(i:ℕ)) % b := by
            simp only [bits,Finset.mem_filter,Finset.mem_range,i.isLt,true_and]
            split <;> omega
          rw [eq]
        _ = n := (sparseRadixTrunc b k n hb).trans (Nat.mod_eq_of_lt (Finset.mem_range.mp hr))
  have filt : (B.filter (fun s => v s ∈ R)).image v = S.filter (fun n => n ∈ R) := by
    rw [← image]
    ext n
    simp only [Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨s,⟨hs,hr⟩,rfl⟩; exact ⟨⟨s,hs,rfl⟩,hr⟩
    · rintro ⟨⟨s,hs,rfl⟩,hr⟩; exact ⟨s,⟨hs,hr⟩,rfl⟩
  refine ⟨(congrArg Finset.card filt.symm).trans (Finset.card_image_of_injOn (inj.mono (Finset.filter_subset _ _))),?_⟩
  rw [← image, Finset.card_image_of_injOn inj]
  simp [B]
