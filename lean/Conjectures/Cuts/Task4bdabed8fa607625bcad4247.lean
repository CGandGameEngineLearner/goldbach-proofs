import Mathlib
namespace PolyFiber
theorem card_le (P : Polynomial ℤ) (hd : 3 ≤ P.natDegree) (m K : ℤ) (hm : m ≠ 0)
    (s : Finset ℕ) (hs : ∀ x ∈ s, m * P.eval (x:ℤ) = K) : s.card ≤ P.natDegree := by
  let Q := Polynomial.C m * P - Polynomial.C K
  have hdQ : Q.natDegree = P.natDegree := by
    dsimp only [Q]; rw [Polynomial.natDegree_sub_C,Polynomial.natDegree_C_mul hm]
  have hn : Q ≠ 0 := by intro h; simp [h] at hdQ; omega
  calc
    s.card ≤ Q.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun n : ℕ => (n:ℤ))
      · intro x hx
        apply Multiset.mem_toFinset.mpr
        apply (Polynomial.mem_roots hn).2
        simp [Polynomial.IsRoot,Q,hs x hx]
      · intro x _ y _ h; exact Int.ofNat_inj.mp h
    _ ≤ Q.roots.card := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' Q
    _ = _ := hdQ
end PolyFiber



namespace PolyPattern
open Finset
abbrev Vec := Fin 4 → ℕ
abbrev Pair := Vec × Vec
abbrev Key (n : ℕ) := (Fin 4 → Option (Fin n)) × (Fin 4 → Fin n)
def support (z : Pair) : Finset ℕ := univ.image z.1 ∪ univ.image z.2
def vec (k : Key n) (v : Fin n → ℕ) (x : ℕ) : Pair :=
  (fun i => ((k.1 i).map v).getD x, fun i => v (k.2 i))
theorem encode (z : Pair) (A : Finset ℕ) (ha : ∀ i, z.1 i ∈ A) (hb : ∀ i, z.2 i ∈ A)
    (hd : ∀ i j, z.1 i ≠ z.2 j) (hn : (support z).card ≤ n+1) :
    ∃ k : Key n, ∃ v ∈ Fintype.piFinset (fun _ : Fin n => A),
      k.1 0 = none ∧ vec k v (z.1 0) = z := by
  classical
  let S := (support z).erase (z.1 0)
  have hx : z.1 0 ∈ support z := mem_union_left _ (mem_image_of_mem _ (mem_univ _))
  have hSc : S.card ≤ n := by dsimp [S]; rw [card_erase_of_mem hx]; omega
  let emb (x : S) : Fin n := Fin.castLE hSc ((S.orderIsoOfFin rfl).symm x)
  have hin : Function.Injective emb := fun x y h => (S.orderIsoOfFin rfl).symm.injective (Fin.ext (congrArg (fun i : Fin n => i.val) h))
  let v (i : Fin n) := if h : ∃ x : S, emb x = i then h.choose.val else z.1 0
  have hv (x : S) : v (emb x) = x.val := by
    dsimp [v]; split
    next h => exact congrArg Subtype.val (hin h.choose_spec)
    next h => exact (h ⟨x,rfl⟩).elim
  have hva : ∀ i, v i ∈ A := by
    intro i; dsimp [v]; split
    next h =>
      have hsup := (mem_erase.mp h.choose.property).2
      rcases mem_union.mp hsup with h|h <;> obtain ⟨j,-,he⟩ := mem_image.mp h
      · exact he ▸ ha j
      · exact he ▸ hb j
    next => exact ha 0
  have hl (i) (h : z.1 i ≠ z.1 0) : z.1 i ∈ S :=
    mem_erase.mpr ⟨h,mem_union_left _ (mem_image_of_mem _ (mem_univ _))⟩
  have hr (i) : z.2 i ∈ S :=
    mem_erase.mpr ⟨(hd 0 i).symm,mem_union_right _ (mem_image_of_mem _ (mem_univ _))⟩
  let l (i : Fin 4) : Option (Fin n) := if h : z.1 i = z.1 0 then none else some (emb ⟨_,hl i h⟩)
  let r (i : Fin 4) := emb ⟨_,hr i⟩
  refine ⟨(l,r),v,Fintype.mem_piFinset.mpr hva,by simp [l],Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
  · by_cases h : z.1 i = z.1 0
    · simp [vec,l,h]
    · simpa [vec,l,h] using hv ⟨_,hl i h⟩
  · exact hv ⟨_,hr i⟩

def mass (P : Polynomial ℤ) (w : Vec) := ∑ i, P.eval (w i : ℤ)

theorem count (P : Polynomial ℤ) (hd : 3 ≤ P.natDegree) (A : Finset ℕ) (G : Finset Pair)
    (n : ℕ) (hG : ∀ z ∈ G, (∀ i, z.1 i ∈ A) ∧ (∀ i, z.2 i ∈ A) ∧
      (∀ i j, z.1 i ≠ z.2 j) ∧ mass P z.1 = mass P z.2 ∧ (support z).card ≤ n+1) :
    G.card ≤ Fintype.card (Key n) * A.card^n * P.natDegree := by
  classical
  let keys := (univ : Finset (Key n)).product (Fintype.piFinset fun _ : Fin n => A)
  let F (kv : Key n × (Fin n → ℕ)) := A.filter fun x =>
    kv.1.1 0 = none ∧ mass P (vec kv.1 kv.2 x).1 = mass P (vec kv.1 kv.2 x).2
  let Z (kv : Key n × (Fin n → ℕ)) := (F kv).image (vec kv.1 kv.2)
  have cover : G ⊆ keys.biUnion Z := by
    intro z hz
    obtain ⟨hl,hr,hdis,he,hs⟩ := hG z hz
    obtain ⟨k,v,hv,hk,hzv⟩ := encode z A hl hr hdis hs
    refine mem_biUnion.mpr ⟨(k,v),mem_product.mpr ⟨mem_univ _,hv⟩,
      mem_image.mpr ⟨z.1 0,mem_filter.mpr ⟨hl 0,hk,?_⟩,hzv⟩⟩
    simpa [hzv] using he
  have hf (kv : Key n × (Fin n → ℕ)) : (Z kv).card ≤ P.natDegree := by
    apply card_image_le.trans
    by_cases hk : kv.1.1 0 = none
    · let I := (univ : Finset (Fin 4)).filter fun i => kv.1.1 i = none
      have hi : 0 < I.card := card_pos.mpr ⟨0,mem_filter.mpr ⟨mem_univ _,hk⟩⟩
      let J := (univ : Finset (Fin 4)) \ I
      let w := vec kv.1 kv.2 0
      apply PolyFiber.card_le P hd (I.card : ℤ) (mass P w.2 - ∑ i ∈ J, P.eval (w.1 i : ℤ)) (by exact_mod_cast hi.ne')
      intro x hx
      have he := (mem_filter.mp hx).2.2
      let z := vec kv.1 kv.2 x
      change mass P z.1 = mass P w.2 at he
      unfold mass at he
      rw [← sum_sdiff (f:=fun i => P.eval (z.1 i : ℤ)) (subset_univ I)] at he
      have hfix : ∀ i ∈ J, z.1 i = w.1 i := by
        intro i h
        have hne : kv.1.1 i ≠ none := fun e => (mem_sdiff.mp h).2 (mem_filter.mpr ⟨mem_univ _,e⟩)
        cases hki : kv.1.1 i <;> simp_all [z,w,vec]
      have hvar : ∀ i ∈ I, z.1 i = x := by
        intro i h
        simp [z,vec,(mem_filter.mp h).2]
      change (∑ i ∈ J, P.eval (z.1 i : ℤ)) + (∑ i ∈ I, P.eval (z.1 i : ℤ)) = _ at he
      rw [sum_congr rfl (fun i hi => by rw [hfix i hi]),
          sum_congr (s₁:=I) (s₂:=I) rfl (fun i hi => by rw [hvar i hi])] at he
      simp only [sum_const,nsmul_eq_mul] at he
      unfold mass
      linarith
    · have hh : F kv = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hk (mem_filter.mp hx).2.1
      simp [hh]
  calc
    G.card ≤ _ := (card_le_card cover).trans card_biUnion_le
    _ ≤ ∑ _ ∈ keys, P.natDegree := sum_le_sum (fun k _ => hf k)
    _ = _ := by simp [keys]
end PolyPattern

theorem Conjectures.Cuts.Task4bdabed8fa607625bcad4247 : ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   have x13 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 → x15.1 ≠ x15.2 → x13.1 x14.1 + x13.1 x14.2 ≠ x13.2 x15.1 + x13.2 x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) ≠ x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)};                   have x14 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ) → Finset ℕ := fun (x14 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) => Finset.image x14.1 Finset.univ ∪ Finset.image x14.2 Finset.univ;                   (↑{x15 ∈ x13 | (x14 x15).card ≤ if x1.natDegree = (3 : ℕ) then (6 : ℕ) else (5 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)
:= by
  classical
  intro P hd ε hε
  let n := if P.natDegree = 3 then 5 else 4
  let C := Fintype.card (PolyPattern.Key n) * P.natDegree
  refine ⟨(C:ℝ)+1,by positivity,?_⟩
  intro M hM A hA T val G H supp
  let S := H.filter fun z => (supp z).card ≤ if P.natDegree = 3 then 6 else 5
  have hc := PolyPattern.count P hd A S n (by
    intro z hz
    obtain ⟨hzH,hsize⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzG,-⟩ := Finset.mem_filter.mp hzH
    obtain ⟨hzT,he,hh⟩ := Finset.mem_filter.mp hzG
    obtain ⟨hl,hr⟩ := Finset.mem_product.mp hzT
    refine ⟨Fintype.mem_piFinset.mp hl,Fintype.mem_piFinset.mp hr,fun i j => hh (i,j),he,?_⟩
    by_cases h : P.natDegree = 3 <;> simpa [n,supp,PolyPattern.support,h] using hsize)
  have hb : S.card ≤ C * A.card ^ n := by simpa [C,Nat.mul_right_comm,Nat.mul_assoc,Nat.mul_left_comm] using hc
  have hM' : (1:ℝ) ≤ (M:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ M by omega)) hε.le
  change (S.card:ℝ) ≤ ((C:ℝ)+1)*(M:ℝ)^ε*(A.card:ℝ)^n
  apply (show (S.card:ℝ) ≤ (C:ℝ)*(A.card:ℝ)^n by exact_mod_cast hb).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    (C:ℝ) ≤ (C:ℝ)+1 := by linarith
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hM'

