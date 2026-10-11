module

public import Mathlib

public section

/-!
# Erdős #824 conditional on smooth successor primes

Let `h(x)` count coprime pairs of positive integers `a < b < x` with equal
sum of divisors. We prove that Hypothesis A⁺, stated explicitly below, implies
`h(x) > x^(2-ε)` for every positive real `ε` and every sufficiently large
natural `x`. A⁺ itself is an assumption, not a proved theorem of this project.

This formalizes the lower-bound part of Theorem 1.3 of the accompanying paper,
adapting the argument of Pollack and Pomerance (2016, Section 6). It does not
formalize the squarefree strengthening or the paper's argument involving the
unrefereed WD preprint. No unconditional resolution of #824 is claimed.

These definitions are written here independently of the proof development;
the only imported library is Mathlib. The deliberate `sorry` below is the
statement to be implemented by `Solution.lean`, not a gap in that solution.
-/

namespace Erdos824

/-- Number of pairs `1 ≤ a < b < x` with coprime coordinates and equal σ₁-values.
Here `ArithmeticFunction.sigma 1` is the ordinary sum-of-divisors function. -/
@[expose] noncomputable def h (x : ℕ) : ℕ :=
  ((Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter
    (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      ArithmeticFunction.sigma 1 p.1 = ArithmeticFunction.sigma 1 p.2)).card

/-- The interval form of A⁺, included to keep the independent definitions in
exactly the same declaration order as the proof library. The result below uses
only `SmoothSuccessorHypWeak`, which drops the lower bound on the prime. -/
@[expose] def SmoothSuccessorHyp : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/4 → ∀ η : ℝ, 0 < η → ∃ y0 : ℝ, ∀ y : ℝ, y0 ≤ y →
    (y ^ (1 - η) : ℝ) ≤ (((Finset.Ioc ⌊2*y-2⌋₊ ⌊5*y⌋₊).filter
        (fun p => p.Prime ∧ ∀ q ∈ (p+1).primeFactors, ((q:ℕ):ℝ) ≤ y ^ δ)).card : ℝ)

/-- Hypothesis A⁺: for each `0 < δ < 1/4` and `η > 0`, all sufficiently large
real `y` have at least `y^(1-η)` primes `p ≤ ⌊5y⌋` for which every prime factor
of `p+1` is at most `y^δ`. The suffix `Weak` distinguishes this from the stronger
interval hypothesis in the proof library; no lower bound on `p` is imposed. -/
@[expose] def SmoothSuccessorHypWeak : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/4 → ∀ η : ℝ, 0 < η → ∃ y0 : ℝ, ∀ y : ℝ, y0 ≤ y →
    (y ^ (1 - η) : ℝ) ≤ (((Finset.Iic ⌊5*y⌋₊).filter
      (fun p => p.Prime ∧ ∀ q ∈ (p+1).primeFactors, ((q:ℕ):ℝ) ≤ y ^ δ)).card : ℝ)

end Erdos824

/-- Assuming A⁺, the number of coprime equal-σ pairs exceeds `x^(2-ε)` for
every positive `ε` and all sufficiently large natural `x`. -/
theorem Palomar824.main_result (H : Erdos824.SmoothSuccessorHypWeak) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      (x : ℝ) ^ (2 - ε) < (Erdos824.h x : ℝ) := by
  sorry
