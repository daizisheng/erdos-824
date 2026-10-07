import Mathlib

/-!
# Erdős #824: definitions

`h x` counts pairs `1 ≤ a < b < x` with `gcd(a,b) = 1` and `σ(a) = σ(b)`.
-/

open ArithmeticFunction

namespace Erdos824

/-- `h(x) = #{(a,b) : 1 ≤ a < b < x, gcd(a,b) = 1, σ a = σ b}`, `σ = σ₁`. -/
noncomputable def h (x : ℕ) : ℕ :=
  ((Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter
    (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ sigma 1 p.1 = sigma 1 p.2)).card

/-- Hypothesis A⁺ (smooth successors) exactly as in the task statement:
for fixed `δ ∈ (0,1/4)`, `η > 0`, and all large `y`, at least `y^(1-η)` primes
`p ∈ (⌊2y-2⌋, ⌊5y⌋]` have every prime factor of `p+1` at most `y^δ`. -/
def SmoothSuccessorHyp : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/4 → ∀ η : ℝ, 0 < η → ∃ y0 : ℝ, ∀ y : ℝ, y0 ≤ y →
    (y ^ (1 - η) : ℝ) ≤ (((Finset.Ioc ⌊2*y-2⌋₊ ⌊5*y⌋₊).filter
        (fun p => p.Prime ∧ ∀ q ∈ (p+1).primeFactors, ((q:ℕ):ℝ) ≤ y ^ δ)).card : ℝ)

/-- Weakened form of A⁺: the lower end `2y-2` is dropped (primes `p ≤ ⌊5y⌋`).
This is implied by `SmoothSuccessorHyp` (see `smoothSuccessorHyp_weak`). -/
def SmoothSuccessorHypWeak : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/4 → ∀ η : ℝ, 0 < η → ∃ y0 : ℝ, ∀ y : ℝ, y0 ≤ y →
    (y ^ (1 - η) : ℝ) ≤ (((Finset.Iic ⌊5*y⌋₊).filter
        (fun p => p.Prime ∧ ∀ q ∈ (p+1).primeFactors, ((q:ℕ):ℝ) ≤ y ^ δ)).card : ℝ)

theorem smoothSuccessorHyp_weak (H : SmoothSuccessorHyp) : SmoothSuccessorHypWeak := by
  intro δ hδ hδ' η hη
  obtain ⟨y0, hy0⟩ := H δ hδ hδ' η hη
  refine ⟨y0, fun y hy => (hy0 y hy).trans ?_⟩
  exact_mod_cast Finset.card_le_card
    (Finset.filter_subset_filter _ (fun p hp => Finset.mem_Iic.2 (Finset.mem_Ioc.1 hp).2))

end Erdos824
