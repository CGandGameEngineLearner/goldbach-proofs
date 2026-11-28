import Mathlib

theorem Conjectures.Goldbach.ReflectedFactorCenters :
∀ (p b h a₁ a₂ c₁ c₂ : ℤ), 0 ≤ b → b^2 < p-b → 0 < h → p-b ≤ a₁ → a₁ ≤ a₂ → p-b ≤ c₁ → c₁ ≤ c₂ → Even (a₁+a₂) → Even (c₁+c₂) → a₁*a₂ = p^2+h → c₁*c₂ = p^2-h → ∃ k u v : ℤ, 0 < k ∧ p*k ≤ h ∧ 0 ≤ u ∧ 0 ≤ v ∧ a₁ = p+k-u ∧ a₂ = p+k+u ∧ c₁ = p-k-v ∧ c₂ = p-k+v ∧ u^2+v^2 = 2*k^2 ∧ |h-2*p*k| ≤ k^2 := by
  intro p b h a₁ a₂ c₁ c₂ hb hpb hh ha hA hc hC ea ec pa pc
  obtain ⟨x,hx⟩ := ea
  obtain ⟨y,hy⟩ := ec
  let k := x-p
  let l := y-p
  let u := x-a₁
  let v := y-c₁
  have form : a₁=p+k-u ∧ a₂=p+k+u ∧ c₁=p+l-v ∧ c₂=p+l+v := by
    dsimp [k,l,u,v]; omega
  obtain ⟨a1,a2,c1,c2⟩ := form
  have hu : 0≤u := by omega
  have hv : 0≤v := by omega
  have hku : u≤b+k := by omega
  have hlv : v≤b+l := by omega
  rw [a1,a2] at pa
  rw [c1,c2] at pc
  have hp : 0<p-b := by nlinarith only [hpb,sq_nonneg b]
  have nonpos : k+l≤0 := by
    by_contra! bad
    have h1 := pow_le_pow_left₀ hu hku 2
    have h2 := pow_le_pow_left₀ hv hlv 2
    have h3 := mul_le_mul_of_nonneg_left (show 1≤k+l by omega) hp.le
    nlinarith only [h1,h2,h3,hpb,pa,pc]
  have total : k+l=0 := by
    by_contra bad
    have kb : -b≤k ∧ k≤b := by omega
    have lb : -b≤l ∧ l≤b := by omega
    have k2 := mul_nonneg (show 0≤b+k by omega) (show 0≤b-k by omega)
    have l2 := mul_nonneg (show 0≤b+l by omega) (show 0≤b-l by omega)
    have t := mul_le_mul_of_nonneg_left (show k+l≤ -1 by omega) (show 0≤p by omega)
    nlinarith only [k2,l2,t,pa,pc,hpb,hb,sq_nonneg u,sq_nonneg v]
  have el : l = -k := by omega
  rw [el] at pc c1 c2 hlv
  have eq : u^2+v^2 = 2*k^2 := by nlinarith only [pa,pc]
  have kp : 0<k := by
    by_contra! bad
    have t := mul_nonpos_of_nonpos_of_nonneg bad (show 0≤2*p+k by omega)
    nlinarith only [t,pa,hh,sq_nonneg u]
  have kh : p*k ≤ h := by
    have bound := mul_nonneg kp.le (show 0≤p-k by omega)
    nlinarith only [bound,pa,eq,sq_nonneg v]
  refine ⟨k,u,v,kp,kh,hu,hv,a1,a2,by omega,by omega,eq,abs_le.mpr ⟨?_,?_⟩⟩
  · nlinarith only [pa,eq,sq_nonneg v]
  · nlinarith only [pa,sq_nonneg u]
