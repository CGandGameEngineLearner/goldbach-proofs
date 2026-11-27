import Mathlib

/-!
The divisibility obstruction is uniform in the small prime. The six existential
repairs use the cube-root form of Pocklington's criterion. See Brillhart, Lehmer
and Selfridge, *New primality criteria and factorizations of 2^m ± 1*, 1975, and
Bhavik Mehta and Kenny Lau's PrimeCert for the formal certificate approach.
-/

set_option maxRecDepth 8192
set_option exponentiation.threshold 512
set_option maxHeartbeats 4000000

namespace Primorial757Proof

open Finset
open Mathlib.Tactic.Primality (powMod powMod_def)

private def goodBase (n a l : ℕ) : Prop :=
  (powMod a ((n - 1) / l) n - 1).Coprime n

private instance (n a l : ℕ) : Decidable (goodBase n a l) := by
  unfold goodBase
  infer_instance

/-- Each prime divisor is one modulo the factored part of `n - 1`. -/
private theorem factor_dvd_prime_sub_one {n F a : ℕ} (hn : 1 < n) (hF : 0 < F)
    (hd : F ∣ n - 1) (ha : powMod a (n - 1) n = 1)
    (hbase : ∀ l ∈ F.primeFactors, goodBase n a l)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) : F ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  let z : ZMod p := a
  have hFull : a ^ (n - 1) ≡ 1 [MOD n] := by
    change _ % n = _
    rw [← powMod_def, ha, Nat.mod_eq_of_lt hn]
  have hz : z ^ (n - 1) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hFull.of_dvd hpn)
    simpa [z, Nat.cast_pow] using h
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : n - 1 ≠ 0)] at hz
    exact zero_ne_one hz
  obtain ⟨c, hc⟩ := orderOf_dvd_of_pow_eq_one hz
  have hFc : F.Coprime c := by
    by_contra h
    obtain ⟨l, hl, hlF, u, hu⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hlmem := Nat.mem_primeFactors.mpr ⟨hl, hlF, hF.ne'⟩
    have hquot : (n - 1) / l = orderOf z * u := by
      calc
        (n - 1) / l = (l * (orderOf z * u)) / l := by
          congr 1
          rw [hc, hu]
          ring
        _ = _ := Nat.mul_div_cancel_left _ hl.pos
    have hz' : z ^ ((n - 1) / l) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ⟨u, hquot⟩
    have hmod : a ^ ((n - 1) / l) ≡ 1 [MOD p] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      simpa [z, Nat.cast_pow] using hz'
    have hres : 1 ≡ powMod a ((n - 1) / l) n [MOD p] := by
      change 1 % p = _ % p
      rw [powMod_def, Nat.mod_mod_of_dvd _ hpn]
      exact hmod.symm
    have hcop := (hbase l hlmem).symm.coprime_dvd_left hpn
    exact (hp.coprime_iff_not_dvd.mp hcop) hres.dvd'
  have hOrder : F ∣ orderOf z := hFc.dvd_of_dvd_mul_right (hc ▸ hd)
  exact hOrder.trans (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hz0))

private def discriminant (n F : ℕ) : ℕ :=
  let R := (n - 1) / F
  (R % (2 * F)) ^ 2 - 8 * (R / (2 * F))

private theorem discriminant_of_pair {A B u : ℕ} (hu : A * B = 2 * u) :
    ∃ d : ℕ, (A + B) ^ 2 - 8 * u = d ^ 2 := by
  have hAux (a b : ℕ) (hle : b ≤ a) (hab : a * b = 2 * u) :
      (a + b) ^ 2 - 8 * u = (a - b) ^ 2 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have h : (b + d + b) ^ 2 = 4 * ((b + d) * b) + d ^ 2 := by ring
    rw [h, hab, show 4 * (2 * u) = 8 * u by ring]
    simp only [Nat.add_sub_cancel_left]
  rcases le_total B A with h | h
  · exact ⟨A - B, hAux A B h hu⟩
  · rw [add_comm A B]
    exact ⟨B - A, hAux B A h (by simpa [mul_comm] using hu)⟩

/-- The cube bound leaves at most two prime factors. A composite then forces a square. -/
private theorem prime_of_cubic_certificate {n F a d : ℕ}
    (hn : 1 < n) (hF : 0 < F) (heven : Even F) (hd : F ∣ n - 1)
    (hcube : n < F ^ 3) (hodd : Odd ((n - 1) / F))
    (ha : powMod a (n - 1) n = 1)
    (hbase : ∀ l ∈ F.primeFactors, goodBase n a l)
    (hlo : d ^ 2 < discriminant n F) (hhi : discriminant n F < (d + 1) ^ 2) :
    n.Prime := by
  have hdiv (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) : F ∣ p - 1 :=
    factor_dvd_prime_sub_one hn hF hd ha hbase hp hpn
  have hge (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) : F + 1 ≤ p := by
    have hp2 := hp.two_le
    have := Nat.le_of_dvd (by omega : 0 < p - 1) (hdiv p hp hpn)
    omega
  by_contra hnp
  let p := n.minFac
  let q := n / p
  have hp : p.Prime := Nat.minFac_prime (by omega : n ≠ 1)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpq : p * q = n := Nat.mul_div_cancel' hpn
  have hqn : q ∣ n := ⟨p, by rw [mul_comm, hpq]⟩
  have hq1 : 1 < q := by
    have hlt : p < n := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
    by_contra! hq
    have := Nat.mul_le_mul_left p hq
    simp only [hpq, mul_one] at this
    omega
  have hq : q.Prime := by
    by_contra hq
    have hr : q.minFac.Prime := Nat.minFac_prime (by omega : q ≠ 1)
    have hrn : q.minFac ∣ n := (Nat.minFac_dvd q).trans hqn
    have hsq : F ^ 2 ≤ q := (Nat.pow_le_pow_left (by
      have := hge q.minFac hr hrn
      omega) 2).trans (Nat.minFac_sq_le_self (by omega) hq)
    have hmul : F * F ^ 2 ≤ p * q := Nat.mul_le_mul (by
      have := hge p hp hpn
      omega) hsq
    rw [hpq, ← pow_succ'] at hmul
    exact (not_le_of_gt hcube) hmul
  obtain ⟨A, hA⟩ := hdiv p hp hpn
  obtain ⟨B, hB⟩ := hdiv q hq hqn
  have hp2 := hp.two_le
  have hp' : p = F * A + 1 := by omega
  have hq' : q = F * B + 1 := by omega
  have hA1 : 1 ≤ A := by
    by_contra! h
    simp [show A = 0 by omega] at hp'
    omega
  have hB1 : 1 ≤ B := by
    by_contra! h
    simp [show B = 0 by omega] at hq'
    omega
  have hR : (n - 1) / F = F * (A * B) + (A + B) := by
    have h : n = F * (F * (A * B) + (A + B)) + 1 := by
      rw [← hpq, hp', hq']
      ring
    rw [h, Nat.add_sub_cancel_right, Nat.mul_div_cancel_left _ hF]
  have hAB : A * B < F := by
    by_contra! h
    have hle : F ^ 3 ≤ n := calc
      F ^ 3 = (F * F) * F := by ring
      _ ≤ (F * F) * (A * B) := Nat.mul_le_mul_left _ h
      _ = (F * A) * (F * B) := by ring
      _ ≤ p * q := by rw [hp', hq']; gcongr <;> omega
      _ = n := hpq
    omega
  have hsum : A + B < 2 * F := by
    have h : A + B ≤ A * B + 1 := by
      obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hA1
      obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hB1
      nlinarith
    omega
  have hABeven : Even (A * B) := by
    have hs : Odd (A + B) := (Nat.odd_add'.mp (hR ▸ hodd)).mpr (heven.mul_right _)
    rw [Nat.odd_add, ← Nat.not_even_iff_odd] at hs
    rw [Nat.even_mul]
    exact (em (Even A)).imp id hs.mp
  obtain ⟨u, hu⟩ := even_iff_exists_two_mul.mp hABeven
  have hR' : (n - 1) / F = (2 * F) * u + (A + B) := by rw [hR, hu]; ring
  have hrem : ((n - 1) / F) % (2 * F) = A + B := by
    rw [hR', Nat.mul_add_mod, Nat.mod_eq_of_lt hsum]
  have hquot : ((n - 1) / F) / (2 * F) = u := by
    rw [hR', Nat.mul_add_div (by omega), Nat.div_eq_of_lt hsum, Nat.add_zero]
  obtain ⟨r, hr⟩ := discriminant_of_pair hu
  have hdisc : discriminant n F = r ^ 2 := by dsimp [discriminant]; rw [hrem, hquot, hr]
  rw [hdisc] at hlo hhi
  have h₁ : d < r := by
    by_contra! h
    exact (not_lt_of_ge (Nat.pow_le_pow_left h 2)) hlo
  have h₂ : r < d + 1 := by
    by_contra! h
    exact (not_lt_of_ge (Nat.pow_le_pow_left h 2)) hhi
  omega


/-- Discharge the prime-factor conditions for the selected 2–3-smooth divisor. -/
private theorem prime_from_smooth_certificate {n i j a d : ℕ} (hi : i ≠ 0)
    (hn : 1 < n) (hd : (2 ^ i * 3 ^ j) ∣ n - 1) (hcube : n < (2 ^ i * 3 ^ j) ^ 3)
    (hodd : Odd ((n - 1) / (2 ^ i * 3 ^ j))) (ha : powMod a (n - 1) n = 1)
    (h2 : goodBase n a 2) (h3 : j ≠ 0 → goodBase n a 3)
    (hlo : d ^ 2 < discriminant n (2 ^ i * 3 ^ j))
    (hhi : discriminant n (2 ^ i * 3 ^ j) < (d + 1) ^ 2) : n.Prime := by
  have heven : Even (2 ^ i : ℕ) := by
    obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [pow_succ]
    exact ⟨2 ^ i', by omega⟩
  refine prime_of_cubic_certificate hn (by positivity) (heven.mul_right _) hd hcube
    hodd ha ?_ hlo hhi
  intro l hl
  have hlp := Nat.prime_of_mem_primeFactors hl
  have hld := Nat.dvd_of_mem_primeFactors hl
  rcases hlp.dvd_mul.mp hld with h | h
  · have hl2 := (Nat.dvd_prime_two_le Nat.prime_two hlp.two_le).mp (hlp.dvd_of_dvd_pow h)
    simpa [hl2] using h2
  · have hj : j ≠ 0 := by
      intro hj
      exact hlp.not_dvd_one (by simpa [hj] using h)
    have hl3 := (Nat.dvd_prime_two_le Nat.prime_three hlp.two_le).mp (hlp.dvd_of_dvd_pow h)
    simpa [hl3] using h3 hj

private def wheel : ℕ := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p

private def wheelBlock (lo width : ℕ) : ℕ :=
  ∏ j ∈ Finset.range width, if (lo + j).Prime then lo + j else 1

private theorem wheelBlock_add (lo s t : ℕ) :
    wheelBlock lo (s + t) = wheelBlock lo s * wheelBlock (lo + s) t := by
  simp only [wheelBlock, Finset.prod_range_add, Nat.add_assoc]

-- Compute short blocks so kernel reduction never traverses the entire wheel at once.
private theorem wheelPrefix32 : wheelBlock 0 32 = 200560490130 := by decide

private theorem wheelPrefix64 : wheelBlock 0 64 =
    117288381359406970983270 := by
  change wheelBlock 0 (32 + 32) = _
  rw [wheelBlock_add, wheelPrefix32]
  have h : wheelBlock (0 + 32) 32 = 584803025179 := by decide
  rw [h]

private theorem wheelPrefix96 : wheelBlock 0 96 =
    23768741896345550770650537601358310 := by
  change wheelBlock 0 (64 + 32) = _
  rw [wheelBlock_add, wheelPrefix64]
  have h : wheelBlock (0 + 64) 32 = 202652143553 := by decide
  rw [h]

private theorem wheelPrefix128 : wheelBlock 0 128 =
    4014476939333036189094441199026045136645885247730 := by
  change wheelBlock 0 (96 + 32) = _
  rw [wheelBlock_add, wheelPrefix96]
  have h : wheelBlock (0 + 96) 32 = 168897325606883 := by decide
  rw [h]

private theorem wheelPrefix160 : wheelBlock 0 160 =
    35375166993717494840635767087951744212057570647889977422429870 := by
  change wheelBlock 0 (128 + 32) = _
  rw [wheelBlock_add, wheelPrefix128]
  have h : wheelBlock (0 + 128) 32 = 8811899415119 := by decide
  rw [h]

private theorem wheelPrefix192 : wheelBlock 0 192 =
    1030893141925860008499560888835674370998623848299590975192766715520279329390 := by
  change wheelBlock 0 (160 + 32) = _
  rw [wheelBlock_add, wheelPrefix160]
  have h : wheelBlock (0 + 160) 32 = 29141718033697 := by decide
  rw [h]

private theorem wheelPrefix224 : wheelBlock 0 224 =
    367009731827331916465034565550136732339800312955331782619462457039988073311157667212930 := by
  change wheelBlock 0 (192 + 32) = _
  rw [wheelBlock_add, wheelPrefix192]
  have h : wheelBlock (0 + 192) 32 = 356011420487 := by decide
  rw [h]

private theorem wheelPrefix256 : wheelBlock 0 256 =
    64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230 := by
  change wheelBlock 0 (224 + 32) = _
  rw [wheelBlock_add, wheelPrefix224]
  have h : wheelBlock (0 + 224) 32 = 175107974924611 := by decide
  rw [h]

private theorem wheelPrefix288 : wheelBlock 0 288 =
    6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970 := by
  change wheelBlock 0 (256 + 32) = _
  rw [wheelBlock_add, wheelPrefix256]
  have h : wheelBlock (0 + 256) 32 = 108538288030848139 := by decide
  rw [h]

private theorem wheelPrefix320 : wheelBlock 0 320 =
    19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570 := by
  change wheelBlock 0 (288 + 32) = _
  rw [wheelBlock_add, wheelPrefix288]
  have h : wheelBlock (0 + 288) 32 = 2775683761181 := by decide
  rw [h]

private theorem wheelPrefix352 : wheelBlock 0 352 =
    261546705642188677527611215060743478325487449257450867559845540208082579687704696223087912212929304531286298200244292923511657074872113330370 := by
  change wheelBlock 0 (320 + 32) = _
  rw [wheelBlock_add, wheelPrefix320]
  have h : wheelBlock (0 + 320) 32 = 13508676341 := by decide
  rw [h]

private theorem wheelPrefix384 : wheelBlock 0 384 =
    658614500390569664024119437665618976500892468548069400648049333237337193956369480811164206516669866807827915645835408481915303111064764635862931579194844130 := by
  change wheelBlock 0 (352 + 32) = _
  rw [wheelBlock_add, wheelPrefix352]
  have h : wheelBlock (0 + 352) 32 = 2518152537128849 := by decide
  rw [h]

private theorem wheelPrefix416 : wheelBlock 0 416 =
    16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610 := by
  change wheelBlock 0 (384 + 32) = _
  rw [wheelBlock_add, wheelPrefix384]
  have h : wheelBlock (0 + 384) 32 = 25328401897 := by decide
  rw [h]

private theorem wheelPrefix448 : wheelBlock 0 448 =
    106799349783510324633088196370154963001649294985563231205816767298822135097700082617263814630462281610668318462376243299771362029792038518622755267843677086440779983634954128409675690 := by
  change wheelBlock 0 (416 + 32) = _
  rw [wheelBlock_add, wheelPrefix416]
  have h : wheelBlock (0 + 416) 32 = 6402204344683229 := by decide
  rw [h]

private theorem wheelPrefix480 : wheelBlock 0 480 =
    1046322248591969947499039362662952313119442645521837107384098209556854703828264398196758421712367190993062011826876505861905813621385722628389241720214572813750754455998751365120185294279180075991830 := by
  change wheelBlock 0 (448 + 32) = _
  rw [wheelBlock_add, wheelPrefix448]
  have h : wheelBlock (0 + 448) 32 = 9797084445859807 := by decide
  rw [h]

private theorem wheelPrefix512 : wheelBlock 0 512 =
    31964081287196888554640742530273949712805599189441373009521636182430667982828077742788853029807931798207106885718293402541861369758591699412090677759187666930105491469725350718941073722934985042092154205321144030 := by
  change wheelBlock 0 (480 + 32) = _
  rw [wheelBlock_add, wheelPrefix480]
  have h : wheelBlock (0 + 480) 32 = 30548983671341 := by decide
  rw [h]

private theorem wheelPrefix544 : wheelBlock 0 544 =
    4711930799906184953162487834760260422020574773409675520188634839616415335845034221205289256705544681972439104097777157991804380284218315038719444943990492579030720635990538452312528339864352999310398481791730017201031090 := by
  change wheelBlock 0 (512 + 32) = _
  rw [wheelBlock_add, wheelPrefix512]
  have h : wheelBlock (0 + 512) 32 = 147413303 := by decide
  rw [h]

private theorem wheelPrefix576 : wheelBlock 0 576 =
    262602099964733578875446350005851493871757481754950934408019647975485255749955737078733246954593517742934367520740039249400227164117047902844401451483907077632236300249642142147473700235499787839033719639795913501546282875643932385070 := by
  change wheelBlock 0 (544 + 32) = _
  rw [wheelBlock_add, wheelPrefix544]
  have h : wheelBlock (0 + 544) 32 = 55731315063023 := by decide
  rw [h]

private theorem wheelPrefix608 : wheelBlock 0 608 =
    11525420726934209845496952504447687595542753389803464814740306425633031741469476436368739126283972333481262273042448031314228147414775791423423373615152170262402199051122890056319818367320658527551127799903791181830760575700829503118451234986910372570 := by
  change wheelBlock 0 (576 + 32) = _
  rw [wheelBlock_add, wheelPrefix576]
  have h : wheelBlock (0 + 576) 32 = 43889293834596251 := by decide
  rw [h]

private theorem wheelPrefix640 : wheelBlock 0 640 =
    1702638442551072365617326631534342245041465988544372563961893321511809758012320472936554398121035062403896046404654753749168137340872368042807946221263167725872661266685741122100016726950864909508767802965271369340352229248204502328104750019252611639587225304330 := by
  change wheelBlock 0 (608 + 32) = _
  rw [wheelBlock_add, wheelPrefix608]
  have h : wheelBlock (0 + 608) 32 = 147728962169 := by decide
  rw [h]

private theorem wheelPrefix672 : wheelBlock 0 672 =
    129150405245356758951128837939389870063162700601269812726926098829920304165120204220589959940818708176830946524771060295498039124201406810520856934647865088430953560875653428566985048570882677821329196481215292503014034401044680012107736697561649621856185162540641496254997701110 := by
  change wheelBlock 0 (640 + 32) = _
  rw [wheelBlock_add, wheelPrefix640]
  have h : wheelBlock (0 + 640) 32 = 75853100704016767 := by decide
  rw [h]

private theorem wheelPrefix704 : wheelBlock 0 704 =
    19467773070115377343221509599623925236459751278180415885837207534756855405403128279156705968461708578168638327032034542684864920135818987044810141311008655898015207220772515212093850725541003213054560185603695585660265284153421684796257245143362498012760214539505870197264858636122745485373430 := by
  change wheelBlock 0 (672 + 32) = _
  rw [wheelBlock_add, wheelPrefix672]
  have h : wheelBlock (0 + 672) 32 = 150737220166913 := by decide
  rw [h]

private theorem wheelPrefix736 : wheelBlock 0 736 =
    5288466848101959839918945547102028321793170651784319188567617728148566328824396484861245008092304604432502852011616970944236712998965578922976926950903943442150218941663031672796340815498578681035812792854237424194169636710372371429686280435869340940595449200949296217005599006643251024181669403586976230 := by
  change wheelBlock 0 (704 + 32) = _
  rw [wheelBlock_add, wheelPrefix704]
  have h : wheelBlock (0 + 704) 32 = 271652377961 := by decide
  rw [h]

private theorem wheelPrefix758 : wheelBlock 0 758 =
    1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507212970 := by
  change wheelBlock 0 (736 + 22) = _
  rw [wheelBlock_add, wheelPrefix736]
  have h : wheelBlock (0 + 736) 22 = 312154118039 := by decide
  rw [h]

private theorem wheel_value : wheel =
    1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507212970 := by
  rw [show wheel = wheelBlock 0 758 by simp [wheel, wheelBlock, Finset.prod_filter]]
  exact wheelPrefix758

private theorem small_prime_obstructed {k p : ℕ} (hk : 1 ≤ k) (hp : p ≤ 757)
    (hpPrime : p.Prime) : ¬(k * wheel - p).Prime := by
  intro h
  have hw : 1514 < wheel := by rw [wheel_value]; decide
  have hn : wheel ≤ k * wheel := by
    simpa only [one_mul] using Nat.mul_le_mul_right wheel hk
  have hlt : p < k * wheel - p := by omega
  have hmem : p ∈ (Finset.range 758).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpPrime⟩
  have hd : p ∣ k * wheel - p :=
    Nat.dvd_sub (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hmem) k) (dvd_refl p)
  exact (ne_of_lt hlt) ((Nat.dvd_prime_two_le h hpPrime.two_le).mp hd)

-- The search chose p − 1 and q − 1 with large known 2–3-smooth divisors.
-- Lean checks each modular power and discriminant bound with kernel reduction.
private def p1 : ℕ :=
    825408352373878727488648036251249991568673233890576468978694421822758293368235774219156875396272380852376422838140570518589362493793161593238597150948887302513439999438130735683703945930702572512412731846982516655136021716668250262491312930179820708885658125651570321940089173618739627340255454905773713877878439937

set_option maxRecDepth 32768 in
private theorem p1_prime : Nat.Prime p1 :=
  prime_from_smooth_certificate (n := p1) (i := 350) (j := 0) (a := 3)
    (d := 2146919933046301766682577077620402782573575863948916996768393173901428681558250350595765755702955574664652)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro h; exact (h rfl).elim)
    (by decide) (by decide)

private def q1 : ℕ :=
    825408352373878727488648036251249991568673233890576468978694421822758293368235774219156875396272380847190275036897862028793537702443305414782312993757062616478099412047444908068960650197714277724369305479945367978102121516611074624415329441737393912666109011167784520237052737824878898024857019481589994224628773033

set_option maxRecDepth 32768 in
private theorem q1_prime : Nat.Prime q1 :=
  prime_from_smooth_certificate (n := q1) (i := 3) (j := 219) (a := 5)
    (d := 4815457642113854670862740055372424027293116861182610125764642701023513727680850654007437819338999693732398)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro _; decide +kernel)
    (by decide) (by decide)

private theorem repair1 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 1 * wheel :=
  ⟨p1, q1, p1_prime, q1_prime, by rw [wheel_value]; decide⟩

private def p2 : ℕ :=
    1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761749401382709481732312083201016061385796883023462931362608509332774591729056447110710416671833316002217436688778006590695999005375657887131295273003197096115218226072429173253128255821641690367332677393284220690890753

set_option maxRecDepth 32768 in
private theorem p2_prime : Nat.Prime p2 :=
  prime_from_smooth_certificate (n := p2) (i := 350) (j := 0) (a := 3)
    (d := 4513373836807293113728595617036909580917617842315153453513365259875060979859613984915815918116444652771788)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro h; exact (h rfl).elim)
    (by decide) (by decide)

private def q2 : ℕ :=
    1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761649732013040595132782682599376411548219158796826480537229473746048379422231058218481840161867157561857217166991259885590467553274115926153448561426046007419055412637255181030694631415409039857616097334131984323535187

set_option maxRecDepth 32768 in
private theorem q2_prime : Nat.Prime q2 :=
  prime_from_smooth_certificate (n := q2) (i := 1) (j := 220) (a := 2)
    (d := 1360628726838220775066131232877787316480076125439211209873221106502288982615438340122819880809327600217772)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro _; decide +kernel)
    (by decide) (by decide)

private theorem repair2 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * wheel :=
  ⟨p2, q2, p2_prime, q2_prime, by rw [wheel_value]; decide⟩

private def p3 : ℕ :=
    2476225057121636182465944108753749974706019701671729406936083265468274880104707322657470626188817142699623665369485627939225967884570333321997762646606035121492174678026636699791925538112290764927103457822782197615997578671968177093570568560008793919029353005735405394988697972167199882948115565986031224790177546241

set_option maxRecDepth 32768 in
private theorem p3_prime : Nat.Prime p3 :=
  prime_from_smooth_certificate (n := p3) (i := 350) (j := 0) (a := 3)
    (d := 683185064820496306982520205152714671530062651348098908373470057859540342387353558554869062869343628796117)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro h; exact (h rfl).elim)
    (by decide) (by decide)

private def q3 : ℕ :=
    2476225057121636182465944108753749974706019701671729406936083265468274880104707322657470626188817142399076428255629669702922732704139067702064967787511814635482443556430090231466068250272959785783242654158001456283716851027869797567149358555742849945625948404722659131542727762163655693147221857176059899517344092669

set_option maxRecDepth 32768 in
private theorem q3_prime : Nat.Prime q3 :=
  prime_from_smooth_certificate (n := q3) (i := 2) (j := 220) (a := 2)
    (d := 5671808370298973705676888914006157247686020021871499810657213907804561365959347113468878981549721804063718)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro _; decide +kernel)
    (by decide) (by decide)

private theorem repair3 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 3 * wheel :=
  ⟨p3, q3, p3_prime, q3_prime, by rw [wheel_value]; decide⟩

private def p4 : ℕ :=
    3301633409495514909954592145004999966274692935562305875914777687291033173472943096876627501585089523589632021987497435614857575194454742367181694368143842576432078608432613765374165934423963059807110524134502504029124646475865442378240879121771150847623754029329097565195343924132944345608517375301667458042640203777

set_option maxRecDepth 32768 in
private theorem p4_prime : Nat.Prime p4 :=
  prime_from_smooth_certificate (n := p4) (i := 350) (j := 0) (a := 3)
    (d := 3231910426371611071875693603242063820970657321084899867613214638434377981538023452281579518440569458953700)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro h; exact (h rfl).elim)
    (by decide) (by decide)

private def q4 : ℕ :=
    3301633409495514909954592145004999966274692935562305875914777687291033173472943096876627501585089523208634769512656294574674025590491125664901946210679957099534079037509688809636492450089704341140017625173209034503827926457251857169385690365897707638583314517948321803513223721641529755851932522247787374367388648103

set_option maxRecDepth 32768 in
private theorem q4_prime : Nat.Prime q4 :=
  prime_from_smooth_certificate (n := q4) (i := 1) (j := 221) (a := 3)
    (d := 7302385998361342975223427924828969764189552870120349281271631726291109420331750883535830405586776968134192)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro _; decide +kernel)
    (by decide) (by decide)

private theorem repair4 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 4 * wheel :=
  ⟨p4, q4, p4_prime, q4_prime, by rw [wheel_value]; decide⟩

private def p5 : ℕ :=
    4127041761869393637443240181256249957843366169452882344893472109113791466841178871095784376981361904257451246402301243852085297416489524519650719084977098298215375944697266781419354834316616235573974688482213880966322062997000913407916935921792535978616360187230970567070439174353201444913591636452919939630435926017

set_option maxRecDepth 32768 in
private theorem p5_prime : Nat.Prime p5 :=
  prime_from_smooth_certificate (n := p5) (i := 350) (j := 0) (a := 3)
    (d := 761232886373700161497626214620645463534275287435320949885578156734746453821753512126761701761214574861588)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro h; exact (h rfl).elim)
    (by decide) (by decide)

private def q5 : ℕ :=
    4127041761869393637443240181256249957843366169452882344893472109113791466841178871095784376981361904240382242972890918884829203564692810520453831638552651296742321112730611437343968146325468015609935498152425542199868653169395711026616275937793537129142475496865803643815270382864891181911970735483898600882100138833

set_option maxRecDepth 32768 in
private theorem q5_prime : Nat.Prime q5 :=
  prime_from_smooth_certificate (n := q5) (i := 4) (j := 219) (a := 10)
    (d := 232430854507852379047116904713706684119660241997148040693236569362882394441894952506440539710531412918061)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro _; decide +kernel)
    (by decide) (by decide)

private theorem repair5 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 5 * wheel :=
  ⟨p5, q5, p5_prime, q5_prime, by rw [wheel_value]; decide⟩

private def p6 : ℕ :=
    4952450114243272364931888217507499949412039403343458813872166530936549760209414645314941252377634285727338317901921630995846810169597406297341721399267980426702692977858219426555102348161004483169824478171380917398652935628571784210669072006051980023815193147785645423928774751730192611294734723816018642811907735553

set_option maxRecDepth 32768 in
private theorem p6_prime : Nat.Prime p6 :=
  prime_from_smooth_certificate (n := p6) (i := 350) (j := 0) (a := 3)
    (d := 3891207744475547011968162202958550783486589335101836986970159514723187752710036581582884275804498576742412)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro h; exact (h rfl).elim)
    (by decide) (by decide)

private def q6 : ℕ :=
    4952450114243272364931888217507499949412039403343458813872166530936549760209414645314941252377634284470061869348308964288450591007821395750783739468967719087246543491055234435960885228609496618250867745790186390400775923771104165110770782225451307705495409673130483629134076716931518540895940122508163605803135542267

set_option maxRecDepth 32768 in
private theorem q6_prime : Nat.Prime q6 :=
  prime_from_smooth_certificate (n := q6) (i := 1) (j := 221) (a := 3)
    (d := 7948596040182333480500070519062582472294954939902634964049498519215592067478903529228727931670850733062998)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro _; decide +kernel)
    (by decide) (by decide)

private theorem repair6 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 6 * wheel :=
  ⟨p6, q6, p6_prime, q6_prime, by rw [wheel_value]; decide⟩

private theorem repair {k : ℕ} (hk : 1 ≤ k) (hk6 : k ≤ 6) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = k * wheel := by
  interval_cases k
  · exact repair1
  · exact repair2
  · exact repair3
  · exact repair4
  · exact repair5
  · exact repair6

end Primorial757Proof

open Primorial757Proof in
theorem Conjectures.Goldbach.Rfc11Primorial757Repairs :
    let W := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p;
    6*W < 10^316 ∧ (10:ℕ)^316 < 7*W ∧ (∀ k : ℕ, 1≤k → k≤6 → let n := k*W;
      (∀ p≤757, p.Prime → ¬ (n-p).Prime) ∧ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)) := by
  dsimp only
  rw [← show wheel = (∏ p ∈ (Finset.range 758).filter Nat.Prime, p) from rfl]
  refine ⟨by rw [wheel_value]; decide, by rw [wheel_value]; decide, ?_⟩
  intro k hk hk6
  exact ⟨fun p hp hprime => small_prime_obstructed hk hp hprime, repair hk hk6⟩
