import Mathlib

namespace WheelPairCount

private def hit (k h : ℕ) : ℕ :=
  if k.Coprime 30 ∧ (k+h).Coprime 30 then 1 else 0

private def count (M h : ℕ) := ∑ k ∈ Finset.range M, hit k h

private def per (h : ℕ) : ℕ :=
  if 2 ∣ h then (if 3 ∣ h then 2 else 1) * (if 5 ∣ h then 4 else 3) else 0

private theorem shiftLag (k h t : ℕ) : hit k (h+30*t) = hit k h := by
  simp only [hit, ← Nat.add_assoc, Nat.coprime_add_mul_left_left]

private theorem shiftIndex (k h t : ℕ) : hit (30*t+k) h = hit k h := by
  rw [Nat.add_comm (30*t) k]
  simp only [hit, show k + 30*t + h = k+h+30*t by omega, Nat.coprime_add_mul_left_left]

/-- The 30 residue classes determine the full period for every lag. -/
private theorem onePeriod (h : ℕ) : count 30 h = per h := by
  have table (a : Fin 30) : count 30 a.val = per a.val := by
    fin_cases a <;> decide
  have h₂ : 2 ∣ h%30 ↔ 2 ∣ h := by omega
  have h₃ : 3 ∣ h%30 ↔ 3 ∣ h := by omega
  have h₅ : 5 ∣ h%30 ↔ 5 ∣ h := by omega
  calc
    count 30 h = count 30 (h%30) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa only [Nat.mod_add_div] using shiftLag k (h%30) (h/30)
    _ = per (h%30) := table ⟨h%30,Nat.mod_lt _ (by decide)⟩
    _ = per h := by simp only [per,h₂,h₃,h₅]

private theorem append (t r h : ℕ) : count (30*t+r) h = count (30*t) h + count r h := by
  simp only [count, Finset.sum_range_add, shiftIndex]

private theorem fullBlocks (t h : ℕ) : count (30*t) h = t * per h := by
  induction t with
  | zero => simp [count]
  | succ t ih => rw [Nat.mul_succ, append, ih, onePeriod, Nat.succ_mul]

private theorem tailBound (r h : ℕ) : count r h ≤ r := by
  calc
    _ ≤ ∑ _k ∈ Finset.range r, 1 := Finset.sum_le_sum (fun k _ => by simp [hit]; split_ifs <;> omega)
    _ = _ := by simp

private theorem perBound (h : ℕ) : per h ≤ 8 := by
  unfold per
  split_ifs <;> decide

end WheelPairCount

open WheelPairCount in
theorem Conjectures.Cuts.Task97f2f73c3f4d394af1f5c84a :
    let w := fun k : ℕ => if k.Coprime 30 then (30:ℝ)/8 else 0
    let ρ := fun h : ℕ => if 2 ∣ h then (15:ℝ)/32 * (if 3 ∣ h then 2 else 1) * (if 5 ∣ h then 4 else 3) else 0
    ∀ M h : ℕ, |(∑ k ∈ Finset.range M, w k * w (k+h)) - (M:ℝ)*ρ h| ≤ 450 := by
  intro w ρ M h
  let t := M/30
  let r := M%30
  have splitM : 30*t+r=M := Nat.div_add_mod M 30
  have splitC : count M h = t*per h + count r h := by
    calc
      count M h = count (30*t+r) h := congrArg (fun a => count a h) splitM.symm
      _ = _ := by rw [append,fullBlocks]
  have countReal : (count M h:ℝ) = (t:ℝ)*(per h:ℝ)+(count r h:ℝ) := by exact_mod_cast splitC
  have lengthReal : (M:ℝ) = 30*(t:ℝ)+(r:ℝ) := by exact_mod_cast splitM.symm
  have rate : ρ h = (15/32:ℝ)*(per h:ℝ) := by
    dsimp only [ρ,per]
    split_ifs <;> norm_num
  have total : (∑ k ∈ Finset.range M, w k * w (k+h)) = (225/16:ℝ)*(count M h:ℝ) := by
    unfold count
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [w,hit]
    split_ifs <;> norm_num <;> tauto
  have rBound : (r:ℝ) ≤ 30 := by exact_mod_cast (Nat.mod_lt M (by decide : 0 < 30)).le
  have cBound : (count r h:ℝ) ≤ r := by exact_mod_cast tailBound r h
  have perLe : (per h:ℝ) ≤ 8 := by exact_mod_cast perBound h
  have prodLe : (r:ℝ)*(per h:ℝ) ≤ 30*8 := mul_le_mul rBound perLe (Nat.cast_nonneg _) (by norm_num)
  rw [total,countReal,lengthReal,rate]
  have cancel :
      (225/16:ℝ)*((t:ℝ)*per h+count r h) - (30*(t:ℝ)+r)*(15/32*per h) =
      (225/16:ℝ)*count r h - (15/32)*((r:ℝ)*per h) := by ring
  rw [cancel, abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (count r h),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) r) (Nat.cast_nonneg (α := ℝ) (per h))]
