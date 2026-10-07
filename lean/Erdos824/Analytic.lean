import Mathlib

/-!
# Erdős #824: pure real-arithmetic steps

All variables are plain reals; the lemmas are later instantiated with
`k = ⌊L/Λ⌋`, `t = ⌈ηk⌉`, `dk = log D - log k`, `lU = log U`, etc.
-/

namespace Erdos824

lemma log_consts : Real.log 6 < 2 ∧ Real.log 5 < 2 ∧ Real.log 4 < 2 ∧
    0 < Real.log 5 ∧ 0 < Real.log 6 := by
  have h6 : Real.log 6 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith
  have h5 := Real.log_lt_log (by norm_num : (0:ℝ) < 5) (by norm_num : (5:ℝ) < 6)
  have h4 := Real.log_lt_log (by norm_num : (0:ℝ) < 4) (by norm_num : (4:ℝ) < 6)
  exact ⟨h6, by linarith, by linarith, Real.log_pos (by norm_num), Real.log_pos (by norm_num)⟩

/-- Bad-pair condition in log form: `log 2 + log U + k log 2 ≤ t (log D - log k)`. -/
lemma bad_ineq (k t ℓ L B η a dk G lU l2 r Λ : ℝ)
    (hk0 : 0 ≤ k) (ht : η * k ≤ t) (hda : a ≤ dk) (ha0 : 0 ≤ a) (ha : a = (B - 2) * ℓ - l2)
    (hBη : B * η = 1) (hη16 : η ≤ 1/16) (hη0 : 0 < η) (hl2 : l2 < 0.7) (hl2p : 0 < l2)
    (hℓ8 : 8 ≤ ℓ) (hB : 16 ≤ B) (hr : r * Λ = L) (hΛ : Λ ≤ 2 * B * ℓ) (hrk : r - 1 ≤ k)
    (hr0 : 0 ≤ r) (hG2 : 12 * B * G ≤ L) (hℓG : ℓ + 1 ≤ G) (hlU : lU ≤ G) :
    l2 + lU + k * l2 ≤ t * dk := by
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have p1 : η * k * a ≤ t * dk := mul_le_mul ht hda ha0 ht0
  have p2 : η * k * a = (B * η) * (k * ℓ) - 2 * η * (k * ℓ) - η * k * l2 := by rw [ha]; ring
  rw [hBη] at p2
  have hkℓ0 : 0 ≤ k * ℓ := mul_nonneg hk0 (by linarith)
  have p3 : η * (k * ℓ) ≤ (1/16) * (k * ℓ) := mul_le_mul_of_nonneg_right hη16 hkℓ0
  have p4' : η * l2 ≤ 1/16 := by nlinarith
  have p4 : η * k * l2 ≤ k / 16 := by
    have := mul_le_mul_of_nonneg_left p4' hk0; linarith
  have p5 : 8 * k ≤ k * ℓ := by nlinarith
  have p6 : k * l2 ≤ 0.7 * k := by nlinarith
  have p7 : (r - 1) * ℓ ≤ k * ℓ := mul_le_mul_of_nonneg_right hrk (by linarith)
  have p8 : r * Λ ≤ r * (2 * B * ℓ) := mul_le_mul_of_nonneg_left hΛ hr0
  have p9 : 2 * B * ((r - 1) * ℓ) ≤ 2 * B * (k * ℓ) :=
    mul_le_mul_of_nonneg_left p7 (by positivity)
  have p10 : 2 * B * (6 * G - ℓ) ≤ 2 * B * (k * ℓ) := by nlinarith
  have p11 : 6 * G - ℓ ≤ k * ℓ := le_of_mul_le_mul_left p10 (by positivity)
  linarith

/-- Main inequality in log form: `(2-ε)L + log 4 + log U + t log Y < 2k (log D - log k)`. -/
lemma main_ineq (k t ℓ L B η ε a dk G lU l2 l4 l5 l6 lY r Λ : ℝ)
    (hk0 : 0 ≤ k) (ha : a = (B - 2) * ℓ - l2) (hda : a ≤ dk) (ht1 : t ≤ η * k + 1)
    (ht0 : 0 ≤ t) (hlY : lY ≤ l5 + B * ℓ) (hlY0 : 0 ≤ lY) (hBη : B * η = 1)
    (hεB : ε * B = 16) (hε : 0 < ε) (hη0 : 0 < η) (hη16 : η ≤ 1/16)
    (hl2 : l2 < 0.7) (_hl2p : 0 < l2) (hl4 : l4 < 2) (hl5 : l5 < 2) (hl5p : 0 < l5)
    (hl6 : l6 < 2) (hl6p : 0 < l6) (hΛdef : Λ = l6 + B * ℓ) (hr : r * Λ = L)
    (hrk : r - 1 ≤ k) (hr0 : 0 ≤ r) (hkΛ : k * Λ ≤ L) (hℓ8 : 8 ≤ ℓ) (hB : 16 ≤ B)
    (hG1 : 8 * (3 * B + 4) * G ≤ 3 * ε * L) (hℓG : ℓ + 1 ≤ G) (hlU : lU ≤ G)
    (hL0 : 0 < L) :
    (2 - ε) * L + (l4 + lU + t * lY) < 2 * k * dk := by
  have q1 : 2 * k * ((B - 2) * ℓ - l2) ≤ 2 * k * dk := by
    rw [← ha]; exact mul_le_mul_of_nonneg_left hda (by positivity)
  have q2 : t * lY ≤ (η * k + 1) * (l5 + B * ℓ) := mul_le_mul ht1 hlY hlY0 (by linarith)
  have q2' : (η * k + 1) * (l5 + B * ℓ) = η * k * l5 + (B * η) * (k * ℓ) + l5 + B * ℓ := by
    ring
  rw [hBη] at q2'
  have q3a : ε * Λ = ε * l6 + 16 * ℓ := by rw [hΛdef]; linear_combination ℓ * hεB
  have q3b : 0 < ε * l6 := mul_pos hε hl6p
  have q3 : (2 - ε / 2) * Λ ≤ (2 * B - 5) * ℓ := by
    have e : (2 - ε / 2) * Λ = 2 * Λ - (ε * Λ) / 2 := by ring
    rw [e, q3a, hΛdef]; linarith
  have q4a : r * ((2 - ε / 2) * Λ) ≤ r * ((2 * B - 5) * ℓ) := mul_le_mul_of_nonneg_left q3 hr0
  have q4b : r * ((2 - ε / 2) * Λ) = (2 - ε / 2) * L := by rw [← hr]; ring
  have hc0 : 0 ≤ (2 * B - 5) * ℓ := mul_nonneg (by linarith) (by linarith)
  have q5 : (r - 1) * ((2 * B - 5) * ℓ) ≤ k * ((2 * B - 5) * ℓ) :=
    mul_le_mul_of_nonneg_right hrk hc0
  have q6a : k * (B * ℓ) ≤ k * Λ := mul_le_mul_of_nonneg_left (by linarith) hk0
  have q6b : ε * (k * (B * ℓ)) ≤ ε * L := mul_le_mul_of_nonneg_left (by linarith) hε.le
  have q6c : ε * (k * (B * ℓ)) = 16 * (k * ℓ) := by linear_combination (k * ℓ) * hεB
  have q7 : k * 8 ≤ k * ℓ := mul_le_mul_of_nonneg_left hℓ8 hk0
  have q8a : η * l5 ≤ 1/16 * 2 := mul_le_mul hη16 hl5.le hl5p.le (by norm_num)
  have q8 : η * k * l5 ≤ k / 8 := by
    have := mul_le_mul_of_nonneg_left q8a hk0; linarith
  have q9 : k * l2 ≤ k * 0.7 := mul_le_mul_of_nonneg_left hl2.le hk0
  have q10 : B * (ℓ + 1) ≤ B * G := mul_le_mul_of_nonneg_left hℓG (by linarith)
  have hεL : 0 < ε * L := mul_pos hε hL0
  linarith

end Erdos824
