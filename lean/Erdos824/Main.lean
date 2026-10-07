import Erdos824.Core
import Erdos824.Analytic

/-!
# Erdős #824 from hypothesis A⁺: analytic part

Parameters (for `0 < ε ≤ 1`): `B = 16/ε`, `η = ε/16` (so `B η = 1`), `δ = 1/(2B)`.
For `x` large, `L = log x`, `ℓ = log L`, `y = L^B`, `Y = ⌊5y⌋`, `s = ⌊y^δ⌋ ≤ √L`,
`Λ = log 6 + B ℓ`, `k = ⌊L/Λ⌋`, `t = ⌈η k⌉`, `U = (log₂ x + 1)^(s+1)`.
-/

open Real Filter Asymptotics

namespace Erdos824

/-- `(√L+1)(log(2L)+1) = o(L)`. -/
lemma master (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, (√L + 1) * (Real.log (2*L) + 1) ≤ c * L := by
  have h1 : (fun L : ℝ => √L + 1) =O[atTop] (fun L => L ^ (1/2:ℝ)) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← Real.sqrt_eq_rpow,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have : 1 ≤ √L := Real.one_le_sqrt.2 hL
    linarith
  have h2 : (fun L : ℝ => Real.log (2*L) + 1) =o[atTop] (fun L => L ^ (1/2:ℝ)) := by
    have hlog := isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)
    have hc : (fun _ : ℝ => Real.log 2 + 1) =o[atTop] (fun L : ℝ => L ^ (1/2:ℝ)) := by
      rw [isLittleO_const_left]
      right
      exact tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (by norm_num))
    refine (hlog.add hc).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    rw [Real.log_mul (by norm_num) hL.ne']; ring
  have h3 := h1.mul_isLittleO h2
  have h4 : (fun L : ℝ => L ^ (1/2:ℝ) * L ^ (1/2:ℝ)) =ᶠ[atTop] (fun L => L) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_add' hL (by norm_num)]; norm_num
  have h5 := (h3.congr' EventuallyEq.rfl h4).bound hc
  filter_upwards [h5, eventually_ge_atTop (1:ℝ)] with L h hL
  have hlog : 0 ≤ Real.log (2*L) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by linarith)] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- The main estimate at one (large) `x`, with all largeness conditions explicit. -/
lemma main_at (ε B η δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : B = 16 / ε) (hη : η = ε / 16)
    (hδ : δ = 1 / (2 * B)) (x : ℕ) (hx : 0 < x) (L : ℝ) (hL : L = Real.log x)
    (hL8 : Real.exp 8 ≤ L)
    (hG1 : 8 * (3*B+4) * ((√L + 1) * (Real.log (2*L) + 1)) ≤ 3 * ε * L)
    (hG2 : 12 * B * ((√L + 1) * (Real.log (2*L) + 1)) ≤ L)
    (P : Finset ℕ)
    (hPdef : P = (Finset.Iic ⌊5*(L^B)⌋₊).filter
        (fun p => p.Prime ∧ ∀ q ∈ (p+1).primeFactors, ((q:ℕ):ℝ) ≤ (L^B) ^ δ))
    (hM : (L^B) ^ (1 - η) ≤ (P.card : ℝ)) :
    (x:ℝ) ^ (2 - ε) < (h x : ℝ) := by
  obtain ⟨hlog6, hlog5, hlog4, hlog5p, hlog6p⟩ := log_consts
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  -- basic parameter facts
  have hBpos : 0 < B := by rw [hB]; positivity
  have hBη : B * η = 1 := by rw [hB, hη]; field_simp
  have hεB : ε * B = 16 := by rw [hB]; field_simp
  have hB16 : 16 ≤ B := by rw [hB, le_div_iff₀ hε]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη16 : η ≤ 1/16 := by rw [hη]; linarith
  have he8 : (2:ℝ) ≤ Real.exp 8 := by have := Real.add_one_le_exp (8:ℝ); linarith
  have hL2 : 2 ≤ L := le_trans he8 hL8
  have hL0 : 0 < L := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log L := ⟨_, rfl⟩
  have hℓ8 : 8 ≤ ℓ := by
    rw [hℓ, ← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hL8
  obtain ⟨y, hy⟩ : ∃ y, y = L ^ B := ⟨_, rfl⟩
  rw [← hy] at hPdef hM
  have hy1 : 1 ≤ y := by rw [hy]; exact Real.one_le_rpow (by linarith) hBpos.le
  have hy0 : 0 < y := by linarith
  have hlogy : Real.log y = B * ℓ := by rw [hy, hℓ]; exact Real.log_rpow hL0 B
  have hyδ : y ^ δ = √L := by
    rw [hy, ← Real.rpow_mul hL0.le, Real.sqrt_eq_rpow, hδ]
    congr 1; field_simp
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ, Y = ⌊5*y⌋₊ := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = ⌊y ^ δ⌋₊ := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log 6 + B * ℓ := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = L / Λ := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌊r⌋₊ := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = ⌈η * k⌉₊ := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = P.card := ⟨_, rfl⟩
  rw [← hMdef] at hM
  have hBℓ8 : 16 * 8 ≤ B * ℓ := mul_le_mul hB16 hℓ8 (by norm_num) hBpos.le
  have hΛpos : 0 < Λ := by rw [hΛ]; linarith
  have hΛle : Λ ≤ 2 * B * ℓ := by rw [hΛ]; linarith
  have hr : r * Λ = L := by rw [hrdef]; field_simp
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hPprop : ∀ p ∈ P, p.Prime ∧ p ≤ Y ∧ ∀ q ∈ (p+1).primeFactors, q ≤ s := by
    intro p hp
    rw [hPdef, Finset.mem_filter, Finset.mem_Iic] at hp
    refine ⟨hp.2.1, hYdef ▸ hp.1, fun q hq => hsdef ▸ Nat.le_floor (hp.2.2 q hq)⟩
  have hsL : (s:ℝ) ≤ √L := by rw [← hyδ, hsdef]; exact Nat.floor_le (by positivity)
  have hY1 : 1 ≤ Y := by rw [hYdef]; exact Nat.le_floor (by push_cast; linarith)
  have hYle : (Y:ℝ) ≤ 5 * y := by rw [hYdef]; exact Nat.floor_le (by positivity)
  have hYpos : (0:ℝ) < Y := by exact_mod_cast hY1
  have hlogY : Real.log Y ≤ Real.log 5 + B * ℓ := by
    rw [← hlogy, ← Real.log_mul (by norm_num) hy0.ne']
    exact Real.log_le_log hYpos hYle
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY1)
  have hk_le : (k:ℝ) ≤ r := by rw [hkdef]; exact Nat.floor_le hr0
  have hrk : r - 1 ≤ (k:ℝ) := by rw [hkdef]; have := Nat.lt_floor_add_one r; linarith
  have hkΛ : (k:ℝ) * Λ ≤ L := by rw [← hr]; exact mul_le_mul_of_nonneg_right hk_le hΛpos.le
  have hk0' : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hkL : (k:ℝ) ≤ L := by
    have : (k:ℝ) * 1 ≤ k * Λ := mul_le_mul_of_nonneg_left (by linarith) hk0'
    linarith
  -- G
  obtain ⟨G, hGdef⟩ : ∃ G, G = (√L + 1) * (Real.log (2*L) + 1) := ⟨_, rfl⟩
  rw [← hGdef] at hG1 hG2
  have hsqrt0 : 0 ≤ √L := Real.sqrt_nonneg L
  have hlog2L : ℓ ≤ Real.log (2*L) := by rw [hℓ]; exact Real.log_le_log hL0 (by linarith)
  have hGe : G = √L * (Real.log (2*L) + 1) + (Real.log (2*L) + 1) := by rw [hGdef]; ring
  have hℓG : ℓ + 1 ≤ G := by
    have : 0 ≤ √L * (Real.log (2*L) + 1) := mul_nonneg hsqrt0 (by linarith)
    linarith
  have hk1 : 1 ≤ k := by
    have p8 : L ≤ 2 * B * (r * ℓ) := by
      have := mul_le_mul_of_nonneg_left hΛle hr0; rw [hr] at this; linarith
    have p9 : 12 * B * (ℓ + 1) ≤ 12 * B * G := mul_le_mul_of_nonneg_left hℓG (by positivity)
    have p10 : 2 * B * (6 * ℓ) ≤ 2 * B * (r * ℓ) := by linarith
    have p11 : 6 * ℓ ≤ r * ℓ := le_of_mul_le_mul_left p10 (by positivity)
    have p12 : 6 ≤ r := le_of_mul_le_mul_right p11 (by linarith)
    have : (1:ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
  have ht_ge : η * k ≤ (t:ℝ) := by rw [htdef]; exact Nat.le_ceil _
  have ht_lt : (t:ℝ) < η * k + 1 := by rw [htdef]; exact Nat.ceil_lt_add_one (by positivity)
  have htk : t ≤ k := by
    rw [htdef]; apply Nat.ceil_le.2
    have := mul_le_mul_of_nonneg_right (show η ≤ 1 by linarith) hk0'; linarith
  -- M bounds
  have hMge : L ^ (B - 1) ≤ (M:ℝ) := by
    have e : y ^ (1 - η) = L ^ (B - 1) := by
      rw [hy, ← Real.rpow_mul hL0.le]; congr 1; linear_combination (-1:ℝ) * hBη
    rw [← e]; exact hM
  have hLLB : L * L ≤ L ^ (B - 1) := by
    have h2 : L ^ (2:ℝ) ≤ L ^ (B - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rwa [Real.rpow_two, sq] at h2
  have hLL : 2 * L ≤ L * L := by nlinarith
  have hkM : k < M := by
    have : (k:ℝ) < M := by linarith
    exact_mod_cast this
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = M - k := ⟨_, rfl⟩
  have hDcast : (D:ℝ) = M - k := by rw [hDdef, Nat.cast_sub hkM.le]
  have hDge : L ^ (B - 1) / 2 ≤ (D:ℝ) := by rw [hDcast]; linarith
  have hLB0 : 0 < L ^ (B - 1) := Real.rpow_pos_of_pos hL0 _
  have hD0 : (0:ℝ) < D := by linarith
  have hlogD : (B - 1) * ℓ - Real.log 2 ≤ Real.log D := by
    have hpos : 0 < L ^ (B - 1) / 2 := by positivity
    have := Real.log_le_log hpos hDge
    rw [Real.log_div hLB0.ne' (by norm_num), Real.log_rpow hL0, ← hℓ] at this
    linarith
  have hlogk : Real.log k ≤ ℓ := by rw [hℓ]; exact Real.log_le_log hk0 hkL
  have hDk : (B - 2) * ℓ - Real.log 2 ≤ Real.log D - Real.log k := by linarith
  have ha0 : 0 ≤ (B - 2) * ℓ - Real.log 2 := by
    have : 14 * 8 ≤ (B - 2) * ℓ := mul_le_mul (by linarith) hℓ8 (by norm_num) (by linarith)
    linarith
  -- U
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ, E = Nat.log 2 x := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℕ, U = (E + 1) ^ (s + 1) := ⟨_, rfl⟩
  have hE : (E:ℝ) * Real.log 2 ≤ L := by
    have h2E : ((2 ^ E : ℕ) : ℝ) ≤ x := by
      rw [hEdef]; exact_mod_cast Nat.pow_log_le_self 2 hx.ne'
    have := Real.log_le_log (by positivity) h2E
    rw [Nat.cast_pow, Real.log_pow] at this
    rw [hL]; push_cast at this; linarith
  have hE1 : (E:ℝ) + 1 ≤ 2 * L := by
    have := mul_le_mul_of_nonneg_left hlog2.le (Nat.cast_nonneg (α := ℝ) E)
    linarith
  have hU0 : (0:ℝ) < U := by rw [hUdef]; positivity
  have hlogU : Real.log U ≤ G := by
    rw [hUdef, Nat.cast_pow, Real.log_pow]
    push_cast
    have h1 : Real.log ((E:ℝ) + 1) ≤ Real.log (2*L) :=
      Real.log_le_log (by positivity) hE1
    have h2 : 0 ≤ Real.log ((E:ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg E : (0:ℝ) ≤ E)])
    have h3 : ((s:ℝ) + 1) * Real.log ((E:ℝ) + 1) ≤ (√L + 1) * Real.log (2*L) :=
      mul_le_mul (by linarith) h1 h2 (by positivity)
    have h4 : (√L + 1) * Real.log (2*L) ≤ G := by
      have e : (√L + 1) * (Real.log (2*L) + 1) = (√L + 1) * Real.log (2*L) + (√L + 1) := by
        ring
      rw [hGdef, e]; linarith
    linarith
  -- the bad-pair condition
  have hbad_log := bad_ineq k t ℓ L B η ((B - 2) * ℓ - Real.log 2)
    (Real.log D - Real.log k) G (Real.log U) (Real.log 2) r Λ hk0' ht_ge hDk ha0 rfl hBη
    hη16 hη0 (by linarith) (by linarith) hℓ8 hB16 hr hΛle hrk hr0 hG2 hℓG hlogU
  have hbad : 2 * U * 2^k * k^t ≤ D^t := by
    have key : Real.log 2 + Real.log U + k * Real.log 2 + t * Real.log k
        ≤ t * Real.log D := by linarith
    have lhs : Real.exp (Real.log 2 + Real.log U + k * Real.log 2 + t * Real.log k)
        = ((2 * U * 2^k * k^t : ℕ) : ℝ) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num), Real.exp_log hU0, Real.exp_log hk0]
      push_cast; ring
    have rhs : Real.exp (t * Real.log D) = ((D^t : ℕ) : ℝ) := by
      rw [Real.exp_nat_mul, Real.exp_log hD0]; push_cast; ring
    have := Real.exp_le_exp.2 key
    rw [lhs, rhs] at this
    exact_mod_cast this
  -- (Y+1)^k ≤ x
  have hYk : (Y + 1)^k ≤ x := by
    have h6y : Real.log (6 * y) = Λ := by rw [Real.log_mul (by norm_num) hy0.ne', hlogy, hΛ]
    have hY6 : ((Y:ℝ) + 1) ≤ 6 * y := by linarith
    have : (((Y + 1)^k : ℕ) : ℝ) ≤ x := by
      push_cast
      calc ((Y:ℝ) + 1)^k ≤ (6 * y)^k := pow_le_pow_left₀ (by positivity) hY6 k
        _ = Real.exp (k * Λ) := by
            rw [Real.exp_nat_mul, ← h6y, Real.exp_log (by positivity)]
        _ ≤ Real.exp L := Real.exp_le_exp.2 hkΛ
        _ = x := by rw [hL, Real.exp_log (by exact_mod_cast hx)]
    exact_mod_cast this
  -- the combinatorial core
  have hbad' : 2 * (Nat.log 2 x + 1)^(s+1) * 2^k * k^t ≤ (P.card - k)^t := by
    rw [hUdef, hEdef, hDdef, hMdef] at hbad; exact hbad
  have hcore := core_final P (fun p hp => (hPprop p hp).1) Y s k t x
    (fun p hp => (hPprop p hp).2.1) (fun p hp => (hPprop p hp).2.2) hYk htk
    (by rw [← hMdef]; exact hkM) hbad'
  rw [← hMdef, ← hEdef, ← hUdef] at hcore
  have hlow := choose_lower M k
  rw [← hDdef] at hlow
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = M.choose k := ⟨_, rfl⟩
  rw [← hNdef] at hcore hlow
  -- main log inequality
  have hmain := main_ineq k t ℓ L B η ε ((B - 2) * ℓ - Real.log 2) (Real.log D - Real.log k)
    G (Real.log U) (Real.log 2) (Real.log 4) (Real.log 5) (Real.log 6) (Real.log Y) r Λ
    hk0' rfl hDk ht_lt.le (Nat.cast_nonneg t) hlogY hlogY0 hBη hεB hε hη0 hη16
    (by linarith) (by linarith) hlog4 hlog5 hlog5p hlog6 hlog6p hΛ hr hrk hr0 hkΛ hℓ8 hB16
    hG1 hℓG hlogU hL0
  have hmain_log : (2 - ε) * L + (Real.log 4 + Real.log U + t * Real.log Y
      + ((2*k : ℕ) : ℝ) * Real.log k) < ((2*k : ℕ) : ℝ) * Real.log D := by
    push_cast; linarith
  -- conclude
  have hC : Real.exp (Real.log 4 + Real.log U + t * Real.log Y
      + ((2*k : ℕ) : ℝ) * Real.log k) = 4 * U * (Y:ℝ)^t * (k:ℝ)^(2*k) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log hU0, Real.exp_log hYpos, Real.exp_log hk0]
  have hDpow : Real.exp (((2*k : ℕ) : ℝ) * Real.log D) = (D:ℝ)^(2*k) := by
    rw [Real.exp_nat_mul, Real.exp_log hD0]
  have hlt := Real.exp_lt_exp.2 hmain_log
  rw [Real.exp_add, hC, hDpow] at hlt
  have hlowR : (D:ℝ)^k ≤ N * (k:ℝ)^k := by exact_mod_cast hlow
  have hcoreR : (N:ℝ)^2 ≤ 4 * U * h x * (Y:ℝ)^t := by exact_mod_cast hcore
  have hD2 : (D:ℝ)^(2*k) ≤ (h x : ℝ) * (4 * U * (Y:ℝ)^t * (k:ℝ)^(2*k)) := by
    have e1 : (D:ℝ)^(2*k) = ((D:ℝ)^k)^2 := by ring
    have e2 : (k:ℝ)^(2*k) = ((k:ℝ)^k)^2 := by ring
    rw [e1, e2]
    calc ((D:ℝ)^k)^2 ≤ (N * (k:ℝ)^k)^2 := pow_le_pow_left₀ (by positivity) hlowR 2
      _ = (N:ℝ)^2 * ((k:ℝ)^k)^2 := by ring
      _ ≤ (4 * U * h x * (Y:ℝ)^t) * ((k:ℝ)^k)^2 :=
          mul_le_mul_of_nonneg_right hcoreR (by positivity)
      _ = (h x : ℝ) * (4 * U * (Y:ℝ)^t * ((k:ℝ)^k)^2) := by ring
  have hCpos : 0 < 4 * (U:ℝ) * (Y:ℝ)^t * (k:ℝ)^(2*k) := by positivity
  have hfinal := lt_of_lt_of_le hlt hD2
  have := lt_of_mul_lt_mul_right hfinal hCpos.le
  have e : Real.log x * (2 - ε) = (2 - ε) * L := by rw [hL]; ring
  rw [Real.rpow_def_of_pos (by exact_mod_cast hx), e]
  exact this

/-- The theorem for `0 < ε ≤ 1`, from the weakened hypothesis. -/
lemma main_small (H : SmoothSuccessorHypWeak) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x → (x:ℝ) ^ (2 - ε) < (h x : ℝ) := by
  set B : ℝ := 16 / ε with hB
  set η : ℝ := ε / 16 with hη
  set δ : ℝ := 1 / (2 * B) with hδ
  have hBpos : 0 < B := by positivity
  have hB16 : 16 ≤ B := by rw [hB, le_div_iff₀ hε]; linarith
  have hδpos : 0 < δ := by positivity
  have hδ14 : δ < 1/4 := by
    rw [hδ, div_lt_iff₀ (by positivity)]; linarith
  obtain ⟨y0, hy0⟩ := H δ hδpos hδ14 η (by positivity)
  obtain ⟨c1, hc1def⟩ : ∃ c : ℝ, c = (3*ε/8) / (3*B+4) := ⟨_, rfl⟩
  obtain ⟨c2, hc2def⟩ : ∃ c : ℝ, c = 1 / (12 * B) := ⟨_, rfl⟩
  have hc1 : 0 < c1 := by rw [hc1def]; positivity
  have hc2 : 0 < c2 := by rw [hc2def]; positivity
  have hev : ∀ᶠ L : ℝ in atTop,
      (√L + 1) * (Real.log (2*L) + 1) ≤ min c1 c2 * L ∧ Real.exp 8 ≤ L ∧ y0 ≤ L ^ B ∧ 0 ≤ L :=
    (master _ (lt_min hc1 hc2)).and ((eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hBpos).eventually_ge_atTop y0).and (eventually_ge_atTop 0)))
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hev
  refine ⟨Real.exp L0, fun x hx => ?_⟩
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx0 : 0 < x := by exact_mod_cast hxpos
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log x := ⟨_, rfl⟩
  have hL0L : L0 ≤ L := by
    rw [hL, ← Real.exp_le_exp, Real.exp_log hxpos]; exact hx
  obtain ⟨hG, hL8, hyL, hLnn⟩ := hL0 L hL0L
  have hG1 : 8 * (3*B+4) * ((√L + 1) * (Real.log (2*L) + 1)) ≤ 3 * ε * L := by
    have h1 := hG.trans (mul_le_mul_of_nonneg_right (min_le_left c1 c2) hLnn)
    have e : 8 * (3*B+4) * (c1 * L) = 3 * ε * L := by
      rw [hc1def]; field_simp
    calc _ ≤ 8 * (3*B+4) * (c1 * L) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := e
  have hG2 : 12 * B * ((√L + 1) * (Real.log (2*L) + 1)) ≤ L := by
    have h1 := hG.trans (mul_le_mul_of_nonneg_right (min_le_right c1 c2) hLnn)
    have e : 12 * B * (c2 * L) = L := by
      rw [hc2def]; field_simp
    calc _ ≤ 12 * B * (c2 * L) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := e
  exact main_at ε B η δ hε hε1 hB hη hδ x hx0 L hL hL8 hG1 hG2 _ rfl (hy0 _ hyL)

/-- **Main theorem (weak hypothesis).** -/
theorem erdos824_of_smoothSuccessorWeak (H : SmoothSuccessorHypWeak) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℕ, X ≤ x → (x:ℝ) ^ (2 - ε) < (h x : ℝ) := by
  intro ε hε
  obtain ⟨X, hX⟩ := main_small H (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  calc (x:ℝ) ^ (2 - ε) ≤ (x:ℝ) ^ (2 - min ε 1) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [min_le_left ε 1])
    _ < h x := hX x (le_trans (le_max_left _ _) hx)

/-- **Main theorem (hypothesis exactly as stated in the task).** -/
theorem erdos824_of_smoothSuccessor (H : SmoothSuccessorHyp) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℕ, X ≤ x → (x:ℝ) ^ (2 - ε) < (h x : ℝ) :=
  erdos824_of_smoothSuccessorWeak (smoothSuccessorHyp_weak H)

end Erdos824
