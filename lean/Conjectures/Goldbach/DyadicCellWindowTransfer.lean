import Mathlib

private theorem cell_bound {H : ℕ} (hH : 0 < H) (a b : ℕ → ℝ)
    (ha : (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, a t)
    (hb : (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, b t) :
    (H:ℝ)/4 + (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
      (a s-a t)*(b s-b t))/(2*H) ≤ ∑ t ∈ Finset.range H, a t*b t := by
  let R := Finset.range H
  have hex (s t : ℕ) : (a s-a t)*(b s-b t) = a s*b s-a s*b t-a t*b s+a t*b t := by ring
  have hid : (∑ s ∈ R, ∑ t ∈ R, (a s-a t)*(b s-b t)) =
      2*((H:ℝ)*(∑ t ∈ R, a t*b t) - (∑ s ∈ R, a s)*(∑ t ∈ R,b t)) := by
    simp only [hex,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
      nsmul_eq_mul,← Finset.mul_sum,← Finset.sum_mul]
    simp only [R,Finset.card_range]
    ring
  change _ + (∑ s ∈ R, ∑ t ∈ R, _)/(2*(H:ℝ)) ≤ _
  rw [hid,add_comm,← le_sub_iff_add_le]
  have hpos : (0:ℝ) < H := by exact_mod_cast hH
  apply (div_le_iff₀ (by positivity)).mpr
  dsimp only [R]
  nlinarith only [mul_le_mul ha hb (by positivity) ((by positivity : (0:ℝ) ≤ H/2).trans ha)]

private theorem flatten (B H : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range B, ∑ t ∈ Finset.range H, f (j*H+t)) =
      ∑ i ∈ Finset.range (B*H), f i := by
  induction B with
  | zero => simp
  | succ B ih => rw [Finset.sum_range_succ,ih,Nat.succ_mul,Finset.sum_range_add]

theorem Conjectures.Goldbach.DyadicCellWindowTransfer :
    let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0;
    ∀ k : ℕ, 12 ≤ k → let n : ℕ := 2^k;
    let H : ℕ := 2^(k-k/4);
    let B : ℕ := 2^(k/4-3);
    let p := fun j t : ℕ => n/2+j*H+t;
    let a := fun j t : ℕ => w (p j t);
    let b := fun j t : ℕ => w (n-p j t);
    (∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) → (n:ℝ)/32 + (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ))) ≤ (∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p)) := by
  intro w k hk n H B p a b hmass
  have hBH : B*H*8 = n := by
    change (2:ℕ)^(k/4-3)*2^(k-k/4)*2^3 = 2^k
    rw [← pow_add,← pow_add]
    congr 1; omega
  have hH : 0 < H := by dsimp [H]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hw (x : ℕ) : 0 ≤ w x := by
    dsimp only [w]; split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
    · rfl
  have hbound (j : ℕ) (hj : j < B) : j*H+H ≤ B*H := by
    simpa [Nat.succ_mul] using Nat.mul_le_mul_right H (Nat.succ_le_of_lt hj)
  have blocks (j : ℕ) (hj : j ∈ Finset.range B) :
      (H:ℝ)/4 + (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (a j s-a j t)*(b j s-b j t))/(2*(H:ℝ)) ≤
        ∑ t ∈ Finset.range H, a j t*b j t := by
    have hbnd := hbound j (Finset.mem_range.mp hj)
    apply cell_bound hH
    · exact hmass (n/2+j*H) (by omega) (by omega)
    · let x := n-(n/2+j*H+H-1)
      have h := hmass x (by dsimp only [x]; omega) (by dsimp only [x]; omega)
      refine h.trans_eq ?_
      rw [← Finset.sum_range_reflect (fun t => w (x+t)) H]
      apply Finset.sum_congr rfl
      intro t ht
      have := Finset.mem_range.mp ht
      change w (x+(H-1-t)) = w (n-(n/2+j*H+t))
      congr 1
      dsimp only [x]; omega
  have hsum := Finset.sum_le_sum blocks
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hreal : (B:ℝ)*H*8 = n := by exact_mod_cast hBH
  have hmain : (B:ℝ)*((H:ℝ)/4) = (n:ℝ)/32 := by linarith only [hreal]
  rw [hmain] at hsum
  apply hsum.trans
  let f := fun i : ℕ => w (n/2+i)*w (n-(n/2+i))
  have heq : (∑ j ∈ Finset.range B, ∑ t ∈ Finset.range H, a j t*b j t) =
      ∑ i ∈ Finset.range (B*H), f i := by
    simpa only [a,b,p,f,Nat.add_assoc] using flatten B H f
  rw [heq]
  let S := (Finset.range (B*H)).image (fun i => n/2+i)
  have hinj : Function.Injective (fun i : ℕ => n/2+i) := fun _ _ h => Nat.add_left_cancel h
  calc _ = ∑ x ∈ S, w x*w (n-x) := by rw [Finset.sum_image hinj.injOn]
       _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
         intro x hx
         obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
         have := Finset.mem_range.mp hi
         exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,by omega⟩)
         (fun x _ _ => mul_nonneg (hw x) (hw _))
