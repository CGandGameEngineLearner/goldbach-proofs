import Mathlib

/-!
# Prime pairs at the first six multiples of the primorial through 757

Every prime at most 757 divides both kW and kW-p. For each of the six
multiples, the tables below give an independently constructed prime pair.
The BLS certificate criterion is from the accepted dyadic endpoint proof,
commit 88d12c634462fdc8c18bca52d59d4e5cab497ac3.
-/
namespace Primorial757

namespace BLS

/-- Auxiliary loop for `powMod`: structural recursion on fuel, binary method. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, acc, _, _, _ => acc
  | fuel + 1, acc, b, e, m =>
    if e = 0 then acc
    else powModAux fuel (if e % 2 = 1 then acc * b % m else acc) (b * b % m) (e / 2) m

/-- Kernel-friendly modular exponentiation (structural recursion on fuel, binary method). -/
def powMod (a e m : ℕ) : ℕ := powModAux (Nat.log2 e + 1) (1 % m) (a % m) e m

theorem powModAux_eq (fuel : ℕ) : ∀ acc b e m : ℕ, acc % m = acc → e < 2 ^ fuel →
    powModAux fuel acc b e m = acc * b ^ e % m := by
  induction fuel with
  | zero =>
    intro acc b e m hacc he
    have he0 : e = 0 := by simpa using he
    subst he0
    simp [powModAux, hacc]
  | succ n ih =>
    intro acc b e m hacc he
    rw [powModAux]
    have he2 : e / 2 < 2 ^ n := by
      rw [pow_succ] at he
      omega
    split_ifs with h0 h1
    · subst h0
      simp [hacc]
    · rw [ih _ _ _ _ (Nat.mod_mod _ _) he2]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
      have hk : (2 * k + 1) / 2 = k := by omega
      rw [hk]
      have h : acc * b % m * (b * b % m) ^ k ≡ acc * b * (b * b) ^ k [MOD m] :=
        (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
      have h2 : acc * b * (b * b) ^ k = acc * b ^ (2 * k + 1) := by ring
      rw [h2] at h
      exact h
    · rw [ih _ _ _ _ hacc he2]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
      have hk : (2 * k) / 2 = k := by omega
      rw [hk]
      have h : acc * (b * b % m) ^ k ≡ acc * (b * b) ^ k [MOD m] :=
        (Nat.ModEq.refl _).mul ((Nat.mod_modEq _ _).pow _)
      have h2 : acc * (b * b) ^ k = acc * b ^ (2 * k) := by ring
      rw [h2] at h
      exact h

theorem powMod_eq (a e m : ℕ) : powMod a e m = a ^ e % m := by
  unfold powMod
  rw [powModAux_eq _ _ _ _ _ (Nat.mod_mod _ _) Nat.lt_log2_self]
  have h : 1 % m * (a % m) ^ e ≡ 1 * a ^ e [MOD m] :=
    (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
  rw [one_mul] at h
  exact h

/-- Certificate check for `N` with `F = ℓ^e ∣ N - 1` and `N < F^3`.
`a` is the witness base, `s` an integer-square-root witness for the discriminant. -/
def check (N ℓ e a s : ℕ) : Bool :=
  let F := ℓ ^ e
  let x := powMod a ((N - 1) / ℓ) N
  let m := (N - 1) / F
  let c1 := m % F
  let c2 := m / F
  decide (1 < N) && decide (0 < e) && decide (N % F = 1) && decide (N < F * F * F) &&
  decide (powMod x ℓ N = 1) && decide (Nat.gcd (x + N - 1) N = 1) &&
  (decide (N ≤ F * F) || decide (c1 * c1 < 4 * c2) ||
    (decide (s * s + 4 * c2 < c1 * c1) && decide (c1 * c1 < (s + 1) * (s + 1) + 4 * c2)))

/-- If `d ∣ n` but `d ∤ n / ℓ` (`ℓ` prime), then the full `ℓ`-part of `n` divides `d`. -/
theorem pow_dvd_of_dvd_of_not_dvd_div {ℓ e d n : ℕ} (hℓ : ℓ.Prime) (hn : ℓ ^ e ∣ n)
    (hd : d ∣ n) (hnd : ¬ d ∣ n / ℓ) : ℓ ^ e ∣ d := by
  obtain ⟨k, rfl⟩ := hd
  have hk : ¬ ℓ ∣ k := by
    rintro ⟨k', rfl⟩
    apply hnd
    rw [show d * (ℓ * k') = ℓ * (d * k') by ring, Nat.mul_div_cancel_left _ hℓ.pos]
    exact dvd_mul_right _ _
  have hc : Nat.Coprime (ℓ ^ e) k :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hk)
  exact hc.dvd_of_dvd_mul_right hn

/-- Pocklington step: every prime factor of `N` is `≡ 1 (mod ℓ^e)`. -/
theorem prime_factor_dvd_sub_one {N ℓ e a r : ℕ} (hℓ : ℓ.Prime) (hN : 1 < N)
    (hF : ℓ ^ e ∣ N - 1) (he : 0 < e)
    (hx : (a ^ ((N - 1) / ℓ) % N) ^ ℓ % N = 1)
    (hg : Nat.gcd (a ^ ((N - 1) / ℓ) % N + N - 1) N = 1)
    (hr : r.Prime) (hrN : r ∣ N) : ℓ ^ e ∣ r - 1 := by
  have := Fact.mk hr
  have hℓN : ℓ ∣ N - 1 := (dvd_pow_self ℓ he.ne').trans hF
  generalize hxdef : a ^ ((N - 1) / ℓ) % N = x at hx hg
  have hxc : (x : ZMod r) = (a : ZMod r) ^ ((N - 1) / ℓ) := by
    have h1 : (x : ZMod r) = ((a ^ ((N - 1) / ℓ) : ℕ) : ZMod r) := by
      rw [ZMod.natCast_eq_natCast_iff, ← hxdef]
      exact (Nat.mod_modEq _ _).of_dvd hrN
    rw [h1, Nat.cast_pow]
  have hxl : (x : ZMod r) ^ ℓ = 1 := by
    have h1 : ((x ^ ℓ : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      rw [ZMod.natCast_eq_natCast_iff]
      have h2 : x ^ ℓ ≡ 1 [MOD N] := by
        unfold Nat.ModEq
        rw [hx, Nat.mod_eq_of_lt hN]
      exact h2.of_dvd hrN
    simpa using h1
  have hne : (x : ZMod r) ≠ 1 := by
    intro h1
    have h2 : ((x + N - 1 : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, h1, (ZMod.natCast_eq_zero_iff N r).mpr hrN]
      simp
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 := Nat.dvd_gcd h2 hrN
    rw [hg] at h3
    exact hr.one_lt.ne' (Nat.dvd_one.mp h3)
  have hpow : (a : ZMod r) ^ (N - 1) = 1 := by
    rw [← Nat.div_mul_cancel hℓN, pow_mul, ← hxc, hxl]
  have ha0 : (a : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hpow
    exact zero_ne_one hpow
  have hd1 : orderOf (a : ZMod r) ∣ N - 1 := orderOf_dvd_of_pow_eq_one hpow
  have hd2 : ¬ orderOf (a : ZMod r) ∣ (N - 1) / ℓ := by
    rw [orderOf_dvd_iff_pow_eq_one, ← hxc]
    exact hne
  have hd3 : orderOf (a : ZMod r) ∣ r - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha0)
  exact (pow_dvd_of_dvd_of_not_dvd_div hℓ hF hd1 hd2).trans hd3

/-- `(α+β)² - 4αβ = (α-β)²` is a perfect square, so it is neither negative nor strictly
between two consecutive squares. -/
theorem square_gap {α β s : ℕ} :
    ¬ ((α + β) * (α + β) < 4 * (α * β)) ∧
    ¬ (s * s + 4 * (α * β) < (α + β) * (α + β) ∧
      (α + β) * (α + β) < (s + 1) * (s + 1) + 4 * (α * β)) := by
  have key : ∀ a d : ℕ,
      ¬ ((a + (a + d)) * (a + (a + d)) < 4 * (a * (a + d))) ∧
      ¬ (s * s + 4 * (a * (a + d)) < (a + (a + d)) * (a + (a + d)) ∧
        (a + (a + d)) * (a + (a + d)) < (s + 1) * (s + 1) + 4 * (a * (a + d))) := by
    intro a d
    have hid : (a + (a + d)) * (a + (a + d)) = d * d + 4 * (a * (a + d)) := by ring
    rw [hid]
    refine ⟨by omega, ?_⟩
    rintro ⟨h1, h2⟩
    have h1' : s * s < d * d := by omega
    have h2' : d * d < (s + 1) * (s + 1) := by omega
    have hsd : s < d := by
      by_contra hc
      have := Nat.mul_le_mul (Nat.le_of_not_lt hc) (Nat.le_of_not_lt hc)
      omega
    have hds : d < s + 1 := by
      by_contra hc
      have := Nat.mul_le_mul (Nat.le_of_not_lt hc) (Nat.le_of_not_lt hc)
      omega
    omega
  rcases le_total α β with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact key α d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := key β d
    rwa [Nat.add_comm (β + d) β, Nat.mul_comm (β + d) β]

theorem check_sound {N ℓ e a s : ℕ} (hℓ : ℓ.Prime) (h : check N ℓ e a s = true) : N.Prime := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, powMod_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hN, he⟩, hmod⟩, hlt⟩, hx⟩, hg⟩, hsq⟩ := h
  generalize hFdef : ℓ ^ e = F at hmod hlt hsq
  have hFpos : 0 < F := by
    rw [← hFdef]
    exact pow_pos hℓ.pos e
  have hF : F ∣ N - 1 := by
    have h1 := Nat.dvd_sub_mod (n := F) N
    rwa [hmod] at h1
  by_contra hNp
  have hr : (N.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨t, ht⟩ := Nat.minFac_dvd N
  generalize N.minFac = r at hr ht
  have hrF : F ∣ r - 1 := by
    rw [← hFdef]
    exact prime_factor_dvd_sub_one hℓ hN (hFdef ▸ hF) he hx hg hr (Dvd.intro t ht.symm)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at ht
    exact hNp (ht ▸ hr)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    omega
  obtain ⟨α, hα⟩ := hrF
  have hr2 := hr.two_le
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hα
    omega
  have hrα : r = F * α + 1 := by omega
  have htF : F ∣ t - 1 := by
    have h1 : N - 1 = F * (α * t) + (t - 1) := by
      have h2 : N = F * (α * t) + t := by
        rw [ht, hrα]
        ring
      omega
    rw [h1] at hF
    exact (Nat.dvd_add_right (dvd_mul_right F (α * t))).mp hF
  obtain ⟨β, hβ⟩ := htF
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hβ
    omega
  have htβ : t = F * β + 1 := by omega
  have hNeq : N = α * β * (F * F) + (α + β) * F + 1 := by
    rw [ht, hrα, htβ]
    ring
  have hαβpos : 1 ≤ α * β := Nat.mul_pos (Nat.pos_of_ne_zero hα0) (Nat.pos_of_ne_zero hβ0)
  have hαβ : α * β < F := by
    by_contra hc
    have h1 : F * (F * F) ≤ α * β * (F * F) := Nat.mul_le_mul_right _ (Nat.le_of_not_lt hc)
    have h2 : F * F * F = F * (F * F) := by ring
    have h3 := Nat.zero_le ((α + β) * F)
    omega
  have hNbig : F * F < N := by
    have h1 : 1 * (F * F) ≤ α * β * (F * F) := Nat.mul_le_mul_right _ hαβpos
    have h3 := Nat.zero_le ((α + β) * F)
    omega
  have hsum1 : α + β ≤ α * β + 1 := by
    obtain ⟨a', rfl⟩ : ∃ a', α = a' + 1 := ⟨α - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', β = b' + 1 := ⟨β - 1, by omega⟩
    have h1 : (a' + 1) * (b' + 1) = a' * b' + a' + b' + 1 := by ring
    omega
  have hsum : α + β < F := by
    by_contra hc
    have h1 : α + β = F := by omega
    have h2 : α * β + 1 = F := by omega
    have h3 : N = F * F * F + 1 := by
      calc N = α * β * (F * F) + (α + β) * F + 1 := hNeq
        _ = (α * β + 1) * (F * F) + 1 := by rw [h1]; ring
        _ = F * F * F + 1 := by rw [h2]; ring
    omega
  have hm : (N - 1) / F = (α + β) + F * (α * β) := by
    apply Nat.div_eq_of_eq_mul_right hFpos
    have h1 : α * β * (F * F) + (α + β) * F = F * ((α + β) + F * (α * β)) := by ring
    omega
  have hc1 : (N - 1) / F % F = α + β := by
    rw [hm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsum]
  have hc2 : (N - 1) / F / F = α * β := by
    rw [hm, Nat.add_mul_div_left _ _ hFpos, Nat.div_eq_of_lt hsum, zero_add]
  rw [hc1, hc2] at hsq
  have hgap := square_gap (α := α) (β := β) (s := s)
  rcases hsq with (h1 | h1) | h1
  · omega
  · exact hgap.1 h1
  · exact hgap.2 h1

end BLS

private def W : ℕ := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p

private theorem w_value : W = 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507212970 := by decide +kernel

private theorem obstruction {k p : ℕ} (hk : 1 ≤ k) (hp : p ≤ 757) (hpp : p.Prime) :
    ¬ (k*W-p).Prime := by
  have hm : p ∈ (Finset.range 758).filter Nat.Prime := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hpp⟩
  have hd : p ∣ W := Finset.dvd_prod_of_mem (fun x : ℕ => x) hm
  have hn : p ∣ k*W := dvd_mul_of_dvd_right hd k
  have hdif := Nat.dvd_sub hn (dvd_refl p)
  have hw : 1515 ≤ W := by rw [w_value]; decide
  have hkw : W ≤ k*W := by simpa using Nat.mul_le_mul_right W hk
  intro bad
  have hEq := (Nat.prime_dvd_prime_iff_eq hpp bad).mp hdif
  omega

private theorem left_1 : Nat.Prime 26151189178936726692773734635792655497328404543327408363029966732979264204625006094866711431781449168409913191740032853475245933088356221432748125522548141835805264403394469569871662714321907960050701276743800455169 :=
  BLS.check_sound (ℓ := 2) (e := 350) (a := 3) (s := 1331421051869170727778856304144812288647433430846686301790471561165008169115590873586882728048883818035052)
    (by norm_num) (by decide +kernel)

private theorem right_1 : Nat.Prime 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761673415508696101705854609165560443811510692505601378541555961572678506311439127658501261705418455332868917014692893205289758033391798550420939169089099003625301014090438782672341571955811043204514336662431358706757801 :=
  BLS.check_sound (ℓ := 3) (e := 221) (a := 5) (s := 1752020574582436854392961719564431946325303831389457938255261831709312727292883321212474023754817560979116)
    (by norm_num) (by decide +kernel)

private theorem pair_1 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=1*W := by
  exact ⟨26151189178936726692773734635792655497328404543327408363029966732979264204625006094866711431781449168409913191740032853475245933088356221432748125522548141835805264403394469569871662714321907960050701276743800455169, 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761673415508696101705854609165560443811510692505601378541555961572678506311439127658501261705418455332868917014692893205289758033391798550420939169089099003625301014090438782672341571955811043204514336662431358706757801, left_1, right_1, by rw [w_value]⟩

private theorem left_2 : Nat.Prime 47708662811603820625226672206329841148896091549782677211354504084811477018008851378239647636006112416905096324538563130922564839091580861851766600107955142428091748230798434299188894450879105658711271706828453445633 :=
  BLS.check_sound (ℓ := 2) (e := 350) (a := 3) (s := 1957847469501471250943927989955795998090373818954248790023426830152204760148159752065728309409679428536936)
    (by norm_num) (by decide +kernel)

private theorem right_2 : Nat.Prime 3301633409495514909954592145004999966274692935562305875914777687291033173472943096876627501585089523351424732938473044469539128186143092867145728739629222626628574738159674269496477814017186064467451657748759444727913155543993810682232422892067829135148391845546961453555849523698342599851119290063455709376560980307 :=
  BLS.check_sound (ℓ := 3) (e := 221) (a := 2) (s := 925660420638201880365797785799498478266047546362702516034345303205688544592391650113087273077557724235347)
    (by norm_num) (by decide +kernel)

private theorem pair_2 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=2*W := by
  exact ⟨47708662811603820625226672206329841148896091549782677211354504084811477018008851378239647636006112416905096324538563130922564839091580861851766600107955142428091748230798434299188894450879105658711271706828453445633, 3301633409495514909954592145004999966274692935562305875914777687291033173472943096876627501585089523351424732938473044469539128186143092867145728739629222626628574738159674269496477814017186064467451657748759444727913155543993810682232422892067829135148391845546961453555849523698342599851119290063455709376560980307, left_2, right_2, by rw [w_value]⟩

private theorem left_3 : Nat.Prime 48893913900573083474606958043878175785894271911347489139554524077418330964053877296175747654507341058953711356283561599973904926228417506708198006698727149955515987424694427031446348652141850501702416449920105971713 :=
  BLS.check_sound (ℓ := 2) (e := 350) (a := 3) (s := 414517660627112554463267432333959835134885315550686955880431336498653287741089798071847377012379560748957)
    (by norm_num) (by decide +kernel)

private theorem right_3 : Nat.Prime 4952450114243272364931888217507499949412039403343458813872166530936549760209414645314941252377634285049806179724542214167541742544831225238168458522770360617420094157038395967204116492209502896203005053027072297616152829725933048432302420407553637165928151454942077101836998702884506923953486921459674674387415667197 :=
  BLS.check_sound (ℓ := 3) (e := 221) (a := 2) (s := 174183975933598536321323172729440358893813998942716601505432061732546770803048589240348313089013227973782)
    (by norm_num) (by decide +kernel)

private theorem pair_3 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=3*W := by
  exact ⟨48893913900573083474606958043878175785894271911347489139554524077418330964053877296175747654507341058953711356283561599973904926228417506708198006698727149955515987424694427031446348652141850501702416449920105971713, 4952450114243272364931888217507499949412039403343458813872166530936549760209414645314941252377634285049806179724542214167541742544831225238168458522770360617420094157038395967204116492209502896203005053027072297616152829725933048432302420407553637165928151454942077101836998702884506923953486921459674674387415667197, left_3, right_3, by rw [w_value]⟩

private theorem left_4 : Nat.Prime 4134928348922589643050797527078804506393815141332634382081172108806906075718894573261178639831852931380882531727038536796590873851129206927077721002568190952550241067263401277998142537648259689586723781932767772673 :=
  BLS.check_sound (ℓ := 2) (e := 350) (a := 3) (s := 201234176620084915091816068204451770839868808781354832119975155651408481792515223458339539402215111287988)
    (by norm_num) (by decide +kernel)

private theorem right_4 : Nat.Prime 6603266818991029819909184290009999932549385871124611751829555374582066346945886193753255003170179046794131863151231140546480803257867063525689825437491165293884985537135396499291763811252488761115275217926829006805914036136526425696497362560591137483638877594727178301445166367776331563812190207962731050477261079207 :=
  BLS.check_sound (ℓ := 3) (e := 221) (a := 5) (s := 1193283849135304258561701556058377856014396513112358368417779825226627307002838867030673087761517095308217)
    (by norm_num) (by decide +kernel)

private theorem pair_4 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=4*W := by
  exact ⟨4134928348922589643050797527078804506393815141332634382081172108806906075718894573261178639831852931380882531727038536796590873851129206927077721002568190952550241067263401277998142537648259689586723781932767772673, 6603266818991029819909184290009999932549385871124611751829555374582066346945886193753255003170179046794131863151231140546480803257867063525689825437491165293884985537135396499291763811252488761115275217926829006805914036136526425696497362560591137483638877594727178301445166367776331563812190207962731050477261079207, left_4, right_4, by rw [w_value]⟩

private theorem left_5 : Nat.Prime 21792558316671612689410377931338487242441784266438838596337456528563448064325962424151367347759130512329834923879725377666387403518342132211813028364729456244337602681434060138625795340329884930421304684197678415873 :=
  BLS.check_sound (ℓ := 2) (e := 350) (a := 3) (s := 2212956407675283171043866895156302686880100295170924682031775003970803572717807875094031521102848394776644)
    (by norm_num) (by decide +kernel)

private theorem right_5 : Nat.Prime 8254083523738787274886480362512499915686732338905764689786944218227582933682357742191568753962723808476040931058520550047504123049843847797662766457090910998620240528864430154437360556490716903424779674304804499286465338500009220916191079647773044743029379439759171529451649418592297286495677441515513856314857648977 :=
  BLS.check_sound (ℓ := 3) (e := 221) (a := 2) (s := 887926334936512886054191540031992602267888947743248454542250168004916596549303122899561422632193795966820)
    (by norm_num) (by decide +kernel)

private theorem pair_5 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=5*W := by
  exact ⟨21792558316671612689410377931338487242441784266438838596337456528563448064325962424151367347759130512329834923879725377666387403518342132211813028364729456244337602681434060138625795340329884930421304684197678415873, 8254083523738787274886480362512499915686732338905764689786944218227582933682357742191568753962723808476040931058520550047504123049843847797662766457090910998620240528864430154437360556490716903424779674304804499286465338500009220916191079647773044743029379439759171529451649418592297286495677441515513856314857648977, left_5, right_5, by rw [w_value]⟩

private theorem left_6 : Nat.Prime 80188261078246170335107919714702869551884453416813948375296912508384963227439465121221629166518412296911227062680904195725890717362226454315947499220697887836927069375997732755025471221878396973349923252069799559169 :=
  BLS.check_sound (ℓ := 2) (e := 350) (a := 3) (s := 1198777720464293830185933024296077566018742705748496964430082891206730450832723928778935306440314363450575)
    (by norm_num) (by decide +kernel)

private theorem right_6 : Nat.Prime 9904900228486544729863776435014999898824078806686917627744333061873099520418829290629882504755268570117211926171984424949189481462715932496241007451421751138652323960528490635076522455548871934902279927050340245118524663673785231959213399915555788508612714983989059677065118713636239930312277872974258996545243718651 :=
  BLS.check_sound (ℓ := 3) (e := 221) (a := 2) (s := 2726300018248529765192123777917943591943900896328880649020302776109163944361954966385172729235565502215628)
    (by norm_num) (by decide +kernel)

private theorem pair_6 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=6*W := by
  exact ⟨80188261078246170335107919714702869551884453416813948375296912508384963227439465121221629166518412296911227062680904195725890717362226454315947499220697887836927069375997732755025471221878396973349923252069799559169, 9904900228486544729863776435014999898824078806686917627744333061873099520418829290629882504755268570117211926171984424949189481462715932496241007451421751138652323960528490635076522455548871934902279927050340245118524663673785231959213399915555788508612714983989059677065118713636239930312277872974258996545243718651, left_6, right_6, by rw [w_value]⟩

private theorem all_pairs (k : ℕ) (hlo : 1 ≤ k) (hhi : k ≤ 6) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=k*W := by
  have h : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_1
  · exact pair_2
  · exact pair_3
  · exact pair_4
  · exact pair_5
  · exact pair_6

private theorem lower : 6*W < 10^316 := by rw [w_value]; decide
private theorem upper : (10:ℕ)^316 < 7*W := by rw [w_value]; decide

theorem result : 6*W < 10^316 ∧ (10:ℕ)^316 < 7*W ∧ (∀ k : ℕ, 1≤k → k≤6 → let n := k*W; (∀ p≤757, p.Prime → ¬ (n-p).Prime) ∧ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)) :=
  ⟨lower, upper, fun k hlo hhi =>
    ⟨fun _ hp hprime => obstruction hlo hp hprime, all_pairs k hlo hhi⟩⟩

end Primorial757

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
theorem Conjectures.Goldbach.Rfc11Primorial757Repairs :
    let W := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p; 6*W < 10^316 ∧ (10:ℕ)^316 < 7*W ∧ (∀ k : ℕ, 1≤k → k≤6 → let n := k*W; (∀ p≤757, p.Prime → ¬ (n-p).Prime) ∧ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)) := Primorial757.result
