import Mathlib

theorem Conjectures.Cuts.Taskdc74960e65f0679d60ddc99b : (by
  classical
  exact ∀ m R : ℕ, R ≤ m →
    let L := (Finset.Icc (m-R) m).filter Nat.Prime
    let H := (Finset.Icc m (m+R)).filter Nat.Prime
    ((∑ p ∈ L, Polynomial.monomial p (1:ℕ))*(∑ q ∈ H, Polynomial.monomial q (1:ℕ))).coeff (2*m) = ((Finset.range (R+1)).filter (fun r => Nat.Prime (m-r) ∧ Nat.Prime (m+r))).card) := by
  classical
  intro m R hR L H
  let G := (Finset.range (R+1)).filter (fun r => Nat.Prime (m-r) ∧ Nat.Prime (m+r))
  let A := L.filter (fun p => 2*m-p ∈ H)
  have im : G.image (fun r => m-r) = A := by
    ext p
    constructor
    · intro h
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hb,hl,hu⟩ := Finset.mem_filter.mp hr
      have hb' := Finset.mem_range.mp hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hl⟩,?_⟩
      rw [show 2*m-(m-r)=m+r by omega]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hu⟩
    · intro h
      obtain ⟨hl,hh⟩ := Finset.mem_filter.mp h
      obtain ⟨hb,pp⟩ := Finset.mem_filter.mp hl
      obtain ⟨hlo,hup⟩ := Finset.mem_Icc.mp hb
      have qp := (Finset.mem_filter.mp hh).2
      have e : m-(m-p)=p := by omega
      refine Finset.mem_image.mpr ⟨m-p,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),e.symm ▸ pp,?_⟩,e⟩
      simpa only [show m+(m-p)=2*m-p by omega] using qp
  have inj : Set.InjOn (fun r : ℕ => m-r) G := by
    intro r hr s hs hh
    have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have h2 := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    dsimp at hh
    omega
  have eqcard : A.card=G.card := by rw [← im, Finset.card_image_of_injOn inj]
  change _=G.card
  rw [← eqcard]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [Polynomial.finsetSum_coeff,Polynomial.monomial_mul_monomial,one_mul,Polynomial.coeff_monomial,Finsupp.single_apply]
  have row (p : ℕ) (hp : p ∈ L) :
      (∑ q ∈ H, if p+q=2*m then 1 else 0 : ℕ) = if 2*m-p ∈ H then 1 else 0 := by
    have hpm := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have eq (q : ℕ) : p+q=2*m ↔ q=2*m-p := by omega
    simp_rw [eq]
    simp
  rw [Finset.sum_congr rfl row]
  simp [A]
