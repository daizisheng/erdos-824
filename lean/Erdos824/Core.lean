import Erdos824.Defs

/-!
# Erdős #824: finite combinatorial core

Given a finite set `P` of primes `p ≤ Y` such that every prime factor of `p+1` is `≤ s`,
let `F` be the `k`-subsets of `P`, `N = #F = C(M,k)`. With `(Y+1)^k ≤ x`:

  `N^2 ≤ (log₂ x + 1)^(s+1) * (h x * (Y^t * 2) + N * (C(k,t) * C(M,k-t)))`.
-/

open Finset ArithmeticFunction

namespace Erdos824

/-- `τ(T) = ∏_{p∈T} (p+1)`, which is `σ(∏_{p∈T} p)` for a set of primes. -/
def tau (T : Finset ℕ) : ℕ := ∏ p ∈ T, (p + 1)

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using this

lemma sigma_prod {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : sigma 1 (∏ p ∈ T, p) = tau T := by
  rw [isMultiplicative_sigma.map_prod_of_prime T hT, tau]
  exact Finset.prod_congr rfl (fun p hp => sigma_one_prime (hT p hp))

lemma tau_pos (T : Finset ℕ) : 0 < tau T := prod_pos (fun p _ => Nat.succ_pos p)

/-- Cauchy–Schwarz / pigeonhole: `#F^2 ≤ #f(F) * #{(a,b) ∈ F² : f a = f b}`. -/
lemma cs_pairs {α β : Type*} [DecidableEq α] [DecidableEq β] (F : Finset α) (f : α → β) :
    F.card ^ 2 ≤ (F.image f).card * ((F ×ˢ F).filter (fun e => f e.1 = f e.2)).card := by
  have h1 : F.card = ∑ s ∈ F.image f, (F.filter (fun a => f a = s)).card :=
    card_eq_sum_card_image f F
  have h2 : ((F ×ˢ F).filter (fun e => f e.1 = f e.2)).card
      = ∑ s ∈ F.image f, (F.filter (fun a => f a = s)).card ^ 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun e => f e.1) (t := F.image f)]
    · apply sum_congr rfl
      intro s _
      rw [sq, ← card_product]
      congr 1
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hs⟩
        exact ⟨⟨ha, hs⟩, hb, hab ▸ hs⟩
      · rintro ⟨⟨ha, hs⟩, hb, hs'⟩
        exact ⟨⟨⟨ha, hb⟩, hs.trans hs'.symm⟩, hs⟩
    · intro e he
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product] at he
      exact mem_coe.2 (mem_image_of_mem f he.1.1)
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

/-- Pairs of `k`-subsets sharing at least `t` elements. -/
lemma card_bad (P : Finset ℕ) (k t : ℕ) :
    (((P.powersetCard k) ×ˢ (P.powersetCard k)).filter (fun e => t ≤ (e.1 ∩ e.2).card)).card
      ≤ (P.powersetCard k).card * (k.choose t * P.card.choose (k - t)) := by
  set F := P.powersetCard k
  have hsub : ((F ×ˢ F).filter (fun e => t ≤ (e.1 ∩ e.2).card)) ⊆
      F.biUnion (fun T => (T.powersetCard t).biUnion
        (fun W => ({T} : Finset (Finset ℕ)) ×ˢ (F.filter (fun T' => W ⊆ T')))) := by
    rintro ⟨T, T'⟩ he
    simp only [mem_filter, mem_product] at he
    obtain ⟨W, hW, hWc⟩ := exists_subset_card_eq he.2
    simp only [mem_biUnion, mem_product, mem_singleton, mem_filter, mem_powersetCard]
    exact ⟨T, he.1.1, W, ⟨hW.trans inter_subset_left, hWc⟩, rfl, he.1.2,
      hW.trans inter_subset_right⟩
  refine (card_le_card hsub).trans ?_
  refine card_biUnion_le.trans ?_
  rw [← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro T hT
  refine card_biUnion_le.trans ?_
  have hTc : T.card = k := (mem_powersetCard.1 hT).2
  have hc : (T.powersetCard t).card = k.choose t := by rw [card_powersetCard, hTc]
  rw [← hc, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro W hW
  rw [card_product, card_singleton, one_mul]
  have hWt : W.card = t := (mem_powersetCard.1 hW).2
  rw [← card_powersetCard]
  apply card_le_card_of_injOn (fun T' => T' \ W)
  · intro T' hT'
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powersetCard, F] at hT'
    simp only [mem_coe, mem_powersetCard]
    obtain ⟨⟨hT'P, hT'c⟩, hWT'⟩ := hT'
    exact ⟨sdiff_subset.trans hT'P, by rw [card_sdiff_of_subset hWT', hT'c, hWt]⟩
  · intro A hA B hB hAB
    simp only [coe_filter, Set.mem_ofPred_eq] at hA hB
    simp only at hAB
    rw [← sdiff_union_of_subset hA.2, ← sdiff_union_of_subset hB.2, hAB]

section primes

variable {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
include hP

lemma pf_prod {S : Finset ℕ} (hS : S ⊆ P) : (∏ p ∈ S, p).primeFactors = S :=
  Nat.primeFactors_prod (fun p hp => hP p (hS hp))

lemma prod_pos' {S : Finset ℕ} (hS : S ⊆ P) : 0 < ∏ p ∈ S, p :=
  prod_pos (fun p hp => (hP p (hS hp)).pos)

lemma sigma_prod' {S : Finset ℕ} (hS : S ⊆ P) : sigma 1 (∏ p ∈ S, p) = tau S :=
  sigma_prod (fun p hp => hP p (hS hp))

lemma coprime_prod {S S' : Finset ℕ} (hS : S ⊆ P) (hS' : S' ⊆ P) (hd : Disjoint S S') :
    Nat.Coprime (∏ p ∈ S, p) (∏ p ∈ S', p) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  rw [Nat.coprime_primes (hP p (hS hp)) (hP q (hS' hq))]
  rintro rfl
  exact disjoint_left.1 hd hp hq

end primes

/-- Pairs of `k`-subsets with equal `τ` sharing fewer than `t` elements inject into
`(pairs counted by h x) × [1, Y^t] × Bool`. -/
lemma card_good (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y k t x : ℕ)
    (hY : ∀ p ∈ P, p ≤ Y) (hx : (Y+1)^k ≤ x) (htk : t ≤ k) :
    (((P.powersetCard k) ×ˢ (P.powersetCard k)).filter
        (fun e => tau e.1 = tau e.2 ∧ (e.1 ∩ e.2).card < t)).card ≤ h x * (Y^t * 2) := by
  classical
  set F := P.powersetCard k
  let u : Finset ℕ × Finset ℕ → ℕ := fun e => ∏ p ∈ e.1 \ e.2, p
  let v : Finset ℕ × Finset ℕ → ℕ := fun e => ∏ p ∈ e.2 \ e.1, p
  let g : Finset ℕ × Finset ℕ → ℕ := fun e => ∏ p ∈ e.1 ∩ e.2, p
  let φ : Finset ℕ × Finset ℕ → (ℕ × ℕ) × (ℕ × Bool) := fun e =>
    ((min (u e) (v e), max (u e) (v e)), (g e, decide (u e < v e)))
  let H := (Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter
    (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ sigma 1 p.1 = sigma 1 p.2)
  have hH : h x = H.card := rfl
  have hcard : (H ×ˢ (Icc 1 (Y^t) ×ˢ (univ : Finset Bool))).card = h x * (Y^t * 2) := by
    simp [card_product, hH]
  rw [← hcard]
  apply card_le_card_of_injOn φ
  · rintro ⟨T, T'⟩ he
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_powersetCard, F] at he
    obtain ⟨⟨⟨hTP, hTk⟩, hT'P, hT'k⟩, hτ, hlt⟩ := he
    have hsd : ((T \ T').card) + (T ∩ T').card = k := by rw [card_sdiff_add_card_inter, hTk]
    have hsd' : ((T' \ T).card) + (T ∩ T').card = k := by
      rw [inter_comm, card_sdiff_add_card_inter, hT'k]
    have hne : (T \ T').Nonempty := by
      rw [← card_pos]; omega
    have hne' : (T' \ T).Nonempty := by
      rw [← card_pos]; omega
    have hk0 : k ≠ 0 := by omega
    have hA : T \ T' ⊆ P := sdiff_subset.trans hTP
    have hB : T' \ T ⊆ P := sdiff_subset.trans hT'P
    have hC : T ∩ T' ⊆ P := inter_subset_left.trans hTP
    obtain ⟨p0, hp0⟩ := hne
    have hY1 : 1 ≤ Y := le_trans (hP p0 (hA hp0)).one_lt.le (hY p0 (hA hp0))
    -- bounds on the products
    have hbound : ∀ S ⊆ P, (∏ p ∈ S, p) ≤ Y ^ S.card := fun S hS =>
      prod_le_pow_card _ _ _ (fun p hp => hY p (hS hp))
    have hlt_x : ∀ S ⊆ P, S.card ≤ k → (∏ p ∈ S, p) < x := by
      intro S hS hSk
      calc (∏ p ∈ S, p) ≤ Y ^ S.card := hbound S hS
        _ ≤ Y ^ k := Nat.pow_le_pow_right hY1 hSk
        _ < (Y+1)^k := Nat.pow_lt_pow_left (Nat.lt_succ_self Y) hk0
        _ ≤ x := hx
    have hu_x : u (T, T') < x := show (∏ p ∈ T \ T', p) < x from hlt_x _ hA (by omega)
    have hv_x : v (T, T') < x := show (∏ p ∈ T' \ T, p) < x from hlt_x _ hB (by omega)
    have hu1 : 1 ≤ u (T, T') := prod_pos' hP hA
    have hv1 : 1 ≤ v (T, T') := prod_pos' hP hB
    have huv : u (T, T') ≠ v (T, T') := by
      intro heq
      have h1 := pf_prod hP hA
      have h2 := pf_prod hP hB
      have : T \ T' = T' \ T := by
        rw [← h1, ← h2]; exact congrArg Nat.primeFactors heq
      have hp0' : p0 ∈ T' \ T := this ▸ hp0
      exact (mem_sdiff.1 hp0).2 (mem_sdiff.1 hp0').1
    have hcop : Nat.Coprime (u (T, T')) (v (T, T')) :=
      coprime_prod hP hA hB (disjoint_sdiff_sdiff)
    have hsig : sigma 1 (u (T, T')) = sigma 1 (v (T, T')) := by
      show sigma 1 (∏ p ∈ T \ T', p) = sigma 1 (∏ p ∈ T' \ T, p)
      rw [sigma_prod' hP hA, sigma_prod' hP hB]
      have e1 : tau (T ∩ T') * tau (T \ T') = tau T := prod_inter_mul_prod_sdiff T T' _
      have e2 : tau (T ∩ T') * tau (T' \ T) = tau T' := by
        rw [inter_comm]; exact prod_inter_mul_prod_sdiff T' T _
      exact Nat.eq_of_mul_eq_mul_left (tau_pos _) (by rw [e1, e2, hτ])
    have hg : g (T, T') ∈ Icc 1 (Y^t) := by
      rw [mem_Icc]
      exact ⟨prod_pos' hP hC, (hbound _ hC).trans (Nat.pow_le_pow_right hY1 hlt.le)⟩
    simp only [φ, coe_product, Set.mem_prod, mem_coe, mem_univ, and_true, H,
      mem_filter, mem_product, mem_Ico]
    refine ⟨?_, hg⟩
    rcases lt_or_gt_of_ne huv with hl | hl
    · rw [min_eq_left hl.le, max_eq_right hl.le]
      exact ⟨⟨⟨hu1, hu_x⟩, hv1, hv_x⟩, hl, hcop, hsig⟩
    · rw [min_eq_right hl.le, max_eq_left hl.le]
      exact ⟨⟨⟨hv1, hv_x⟩, hu1, hu_x⟩, hl, hcop.symm, hsig.symm⟩
  · rintro ⟨T1, T1'⟩ he1 ⟨T2, T2'⟩ he2 hφ
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_powersetCard, F] at he1 he2
    simp only [φ, Prod.mk.injEq] at hφ
    obtain ⟨⟨hmin, hmax⟩, hg, hdec⟩ := hφ
    have huv : u (T1, T1') = u (T2, T2') ∧ v (T1, T1') = v (T2, T2') := by
      by_cases h1 : u (T1, T1') < v (T1, T1')
      · have h2 : u (T2, T2') < v (T2, T2') := by simpa [h1] using hdec
        rw [min_eq_left h1.le, min_eq_left h2.le] at hmin
        rw [max_eq_right h1.le, max_eq_right h2.le] at hmax
        exact ⟨hmin, hmax⟩
      · have h2 : ¬ u (T2, T2') < v (T2, T2') := by simpa [h1] using hdec
        push Not at h1 h2
        rw [min_eq_right h1, min_eq_right h2] at hmin
        rw [max_eq_left h1, max_eq_left h2] at hmax
        exact ⟨hmax, hmin⟩
    have hA : T1 \ T1' = T2 \ T2' := by
      rw [← pf_prod hP (sdiff_subset.trans he1.1.1.1),
        ← pf_prod hP (sdiff_subset.trans he2.1.1.1)]
      exact congrArg Nat.primeFactors huv.1
    have hB : T1' \ T1 = T2' \ T2 := by
      rw [← pf_prod hP (sdiff_subset.trans he1.1.2.1),
        ← pf_prod hP (sdiff_subset.trans he2.1.2.1)]
      exact congrArg Nat.primeFactors huv.2
    have hC : T1 ∩ T1' = T2 ∩ T2' := by
      rw [← pf_prod hP (inter_subset_left.trans he1.1.1.1),
        ← pf_prod hP (inter_subset_left.trans he2.1.1.1)]
      exact congrArg Nat.primeFactors hg
    have e1 : T1 = T2 := by
      rw [← sdiff_union_inter T1 T1', ← sdiff_union_inter T2 T2', hA, hC]
    have e2 : T1' = T2' := by
      rw [← sdiff_union_inter T1' T1, ← sdiff_union_inter T2' T2, hB, inter_comm, hC,
        inter_comm]
    rw [e1, e2]

/-- Values of `τ` on `k`-subsets are `s`-smooth and `≤ x`; there are at most
`(log₂ x + 1)^(s+1)` of them. -/
lemma card_image_tau (P : Finset ℕ) (Y s k x : ℕ)
    (hY : ∀ p ∈ P, p ≤ Y) (hs : ∀ p ∈ P, ∀ q ∈ (p+1).primeFactors, q ≤ s)
    (hx : (Y+1)^k ≤ x) :
    ((P.powersetCard k).image tau).card ≤ (Nat.log 2 x + 1) ^ (s + 1) := by
  have key : ∀ n ∈ (P.powersetCard k).image tau,
      n ≠ 0 ∧ n ≤ x ∧ ∀ q ∈ n.primeFactors, q ≤ s := by
    intro n hn
    obtain ⟨T, hT, rfl⟩ := mem_image.1 hn
    rw [mem_powersetCard] at hT
    refine ⟨(tau_pos T).ne', ?_, ?_⟩
    · calc tau T ≤ (Y+1)^T.card :=
            prod_le_pow_card _ _ _ (fun p hp => by have := hY p (hT.1 hp); omega)
        _ = (Y+1)^k := by rw [hT.2]
        _ ≤ x := hx
    · intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqd := Nat.dvd_of_mem_primeFactors hq
      obtain ⟨p, hp, hqp'⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
      exact hs p (hT.1 hp) q (Nat.mem_primeFactors.2 ⟨hqp, hqp', Nat.succ_ne_zero p⟩)
  calc _ ≤ (Fintype.piFinset (fun _ : Fin (s+1) => range (Nat.log 2 x + 1))).card := by
        apply card_le_card_of_injOn (fun n => fun i : Fin (s+1) => n.factorization i)
        · intro n hn
          rw [mem_coe] at hn
          obtain ⟨hn0, hnx, -⟩ := key n hn
          simp only [mem_coe, Fintype.mem_piFinset, mem_range]
          intro i
          rw [Nat.lt_succ_iff]
          by_cases hi : (i:ℕ).Prime
          · apply Nat.le_log_of_pow_le one_lt_two
            calc 2 ^ n.factorization i ≤ (i:ℕ) ^ n.factorization i :=
                  Nat.pow_le_pow_left hi.two_le _
              _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.ordProj_dvd n i)
              _ ≤ x := hnx
          · simp [Nat.factorization_eq_zero_of_not_prime n hi]
        · intro a ha b hb hab
          rw [mem_coe] at ha hb
          obtain ⟨ha0, -, has⟩ := key a ha
          obtain ⟨hb0, -, hbs⟩ := key b hb
          apply Nat.eq_of_factorization_eq ha0 hb0
          intro q
          by_cases hq : q ≤ s
          · have := congrFun hab ⟨q, Nat.lt_succ_of_le hq⟩
            simpa using this
          · have h1 : a.factorization q = 0 := by
              by_contra hne
              exact hq (has q (by rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 hne))
            have h2 : b.factorization q = 0 := by
              by_contra hne
              exact hq (hbs q (by rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 hne))
            rw [h1, h2]
    _ = _ := by simp

/-- **Combinatorial core.** -/
theorem core (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y s k t x : ℕ)
    (hY : ∀ p ∈ P, p ≤ Y) (hs : ∀ p ∈ P, ∀ q ∈ (p+1).primeFactors, q ≤ s)
    (hx : (Y+1)^k ≤ x) (htk : t ≤ k) :
    (P.card.choose k)^2 ≤ (Nat.log 2 x + 1)^(s+1) *
      (h x * (Y^t * 2) + P.card.choose k * (k.choose t * P.card.choose (k-t))) := by
  classical
  set F := P.powersetCard k
  have hF : F.card = P.card.choose k := card_powersetCard k P
  rw [← hF]
  refine (cs_pairs F tau).trans (Nat.mul_le_mul (card_image_tau P Y s k x hY hs hx) ?_)
  have hsub : ((F ×ˢ F).filter (fun e => tau e.1 = tau e.2)) ⊆ ((F ×ˢ F).filter
      (fun e => tau e.1 = tau e.2 ∧ (e.1 ∩ e.2).card < t)) ∪
      ((F ×ˢ F).filter (fun e => t ≤ (e.1 ∩ e.2).card)) := by
    intro e he
    simp only [mem_filter, mem_union] at he ⊢
    by_cases hlt : (e.1 ∩ e.2).card < t
    · exact Or.inl ⟨he.1, he.2, hlt⟩
    · exact Or.inr ⟨he.1, not_lt.1 hlt⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
  · exact card_good P hP Y k t x hY hx htk
  · exact card_bad P k t

/-- `C(M,k-t) * (M-k)^t ≤ C(M,k) * k^t` for `t ≤ k`. -/
lemma choose_ratio (M k : ℕ) : ∀ t, t ≤ k →
    M.choose (k - t) * (M - k)^t ≤ M.choose k * k^t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ih := ih (by omega)
    set j := k - (t+1) with hj
    have hjk : j + 1 = k - t := by omega
    have hrec := Nat.choose_succ_right_eq M j
    rw [hjk] at hrec
    -- C(M,j) * (M-k) ≤ C(M,j) * (M-j) = C(M,k-t) * (k-t) ≤ C(M,k-t) * k
    have step : M.choose j * (M - k) ≤ M.choose (k - t) * k := by
      calc M.choose j * (M - k) ≤ M.choose j * (M - j) := Nat.mul_le_mul_left _ (by omega)
        _ = M.choose (k - t) * (k - t) := by rw [hrec]
        _ ≤ M.choose (k - t) * k := Nat.mul_le_mul_left _ (by omega)
    calc M.choose j * (M - k) ^ (t+1) = (M.choose j * (M - k)) * (M - k)^t := by ring
      _ ≤ (M.choose (k - t) * k) * (M - k)^t := Nat.mul_le_mul_right _ step
      _ = k * (M.choose (k - t) * (M - k)^t) := by ring
      _ ≤ k * (M.choose k * k^t) := Nat.mul_le_mul_left _ ih
      _ = M.choose k * k^(t+1) := by ring

/-- `(M-k)^k ≤ C(M,k) * k^k`. -/
lemma choose_lower (M k : ℕ) : (M - k)^k ≤ M.choose k * k^k := by
  calc (M - k)^k ≤ (M + 1 - k)^k := Nat.pow_le_pow_left (by omega) _
    _ ≤ M.descFactorial k := Nat.pow_sub_le_descFactorial M k
    _ = k.factorial * M.choose k := Nat.descFactorial_eq_factorial_mul_choose M k
    _ ≤ k^k * M.choose k := Nat.mul_le_mul_right _ (Nat.factorial_le_pow k)
    _ = M.choose k * k^k := by ring

/-- Pure arithmetic: removing the bad pairs. -/
lemma arith (N U H G c b D K E : ℕ) (h1 : N^2 ≤ U * (H * (G * 2) + N * (c * b)))
    (h2 : c ≤ E) (h3 : b * D ≤ N * K) (h4 : 2 * U * E * K ≤ D) (hD : 0 < D) :
    N^2 ≤ 4 * U * H * G := by
  have s1 : N^2 * D ≤ 2 * U * H * G * D + N^2 * (U * E * K) := by
    calc N^2 * D ≤ U * (H * (G * 2) + N * (c * b)) * D := Nat.mul_le_mul_right _ h1
      _ = 2 * U * H * G * D + U * N * c * (b * D) := by ring
      _ ≤ 2 * U * H * G * D + U * N * E * (N * K) := by
          apply Nat.add_le_add_left
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h3
      _ = 2 * U * H * G * D + N^2 * (U * E * K) := by ring
  have s2 : 2 * (N^2 * (U * E * K)) ≤ N^2 * D := by
    calc 2 * (N^2 * (U * E * K)) = N^2 * (2 * U * E * K) := by ring
      _ ≤ N^2 * D := Nat.mul_le_mul_left _ h4
  have s3 : N^2 * D ≤ (4 * U * H * G) * D := by nlinarith
  exact Nat.le_of_mul_le_mul_right s3 hD

/-- **Core, final form**: if the bad-pair condition `2 U 2^k k^t ≤ (M-k)^t` holds, then
`C(M,k)^2 ≤ 4 U h(x) Y^t`, with `U = (log₂ x + 1)^(s+1)`. -/
theorem core_final (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y s k t x : ℕ)
    (hY : ∀ p ∈ P, p ≤ Y) (hs : ∀ p ∈ P, ∀ q ∈ (p+1).primeFactors, q ≤ s)
    (hx : (Y+1)^k ≤ x) (htk : t ≤ k) (hkM : k < P.card)
    (hbad : 2 * (Nat.log 2 x + 1)^(s+1) * 2^k * k^t ≤ (P.card - k)^t) :
    (P.card.choose k)^2 ≤ 4 * (Nat.log 2 x + 1)^(s+1) * h x * Y^t :=
  arith _ _ _ _ _ _ _ _ _ (core P hP Y s k t x hY hs hx htk) (Nat.choose_le_two_pow k t)
    (choose_ratio P.card k t htk) hbad (pow_pos (by omega) _)

end Erdos824
