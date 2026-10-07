# Erdős Problem #824: coprime pairs with equal sum of divisors

Let h(x) be the number of pairs 1 ≤ a < b < x with gcd(a,b) = 1 and σ(a) = σ(b), where σ is the sum of divisors. Erdős asked whether h(x) > x^{2−o(1)}.

**Theorem 1 (Lean-verified).** Suppose that for every fixed δ ∈ (0, 1/4) there are at least y^{1−o(1)} primes p ≤ 5y with P⁺(p+1) ≤ y^δ (Hypothesis A⁺, "smooth successors"). Then h(x) > x^{2−ε} for every ε > 0 and all large x; the pairs can be taken squarefree. This is the argument of Pollack–Pomerance (2016, §6), written out with explicit parameters.

**Theorem 2 (conditional on an unrefereed preprint).** The proof of Theorem 1.2 of OpenAI's preprint *Weighted dilation graphs, smooth shifted primes and totient fibers* (2026-09-24, "WD"), which gives smooth *predecessors* p−1, proves A⁺ after a change of sign in its Sections 6–7; Appendix A of the paper lists every change. Hence h(x) = x^{2−o(1)} **if the argument of WD is correct.** WD's Sections 3–5 (transference, ideal operator, shift cancellation) have not been independently verified.

Contents:
- `paper/erdos824.tex` — the paper. It is a draft; audit in progress.
- `lean/` — a Lean 4 formalization of Theorem 1, with no `sorry`.

## Checking the Lean proof

```
cd lean
lake exe cache get      # Mathlib build cache
lake build
lake env lean Check.lean
```
`Check.lean` prints the definitions and statements, and
```
'Erdos824.erdos824_of_smoothSuccessor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos824.erdos824_of_smoothSuccessorWeak' depends on axioms: [propext, Classical.choice, Quot.sound]
```
There is no `sorry` and there are no project axioms. Toolchain `leanprover/lean4:v4.33.1`, Mathlib `0df444a`.

The main statements are:
```lean
noncomputable def h (x : ℕ) : ℕ :=
  ((Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter
    (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ sigma 1 p.1 = sigma 1 p.2)).card

-- Hypothesis A⁺ (the form used by the proof; SmoothSuccessorHyp additionally asks p > 2y−2)
def SmoothSuccessorHypWeak : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/4 → ∀ η : ℝ, 0 < η → ∃ y0 : ℝ, ∀ y : ℝ, y0 ≤ y →
    (y ^ (1 - η) : ℝ) ≤ (((Finset.Iic ⌊5*y⌋₊).filter
      (fun p => p.Prime ∧ ∀ q ∈ (p+1).primeFactors, ((q:ℕ):ℝ) ≤ y ^ δ)).card : ℝ)

theorem erdos824_of_smoothSuccessorWeak (H : SmoothSuccessorHypWeak) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℕ, X ≤ x → (x:ℝ) ^ (2 - ε) < (h x : ℝ)
theorem erdos824_of_smoothSuccessor (H : SmoothSuccessorHyp) : -- same conclusion
```
`sigma 1` is Mathlib's `ArithmeticFunction.sigma 1` (σ₁). Since h(x) depends only on the integers below x, the statement for integer x gives it for real x.

| file | content |
|---|---|
| `Defs.lean` | `h`, `SmoothSuccessorHyp`, `SmoothSuccessorHypWeak`, and the implication between them |
| `Core.lean` | the finite counting: Cauchy–Schwarz over σ-values, the bound for pairs sharing many primes, the gcd-removal injection, binomial bounds |
| `Analytic.lean` | real inequalities for the parameter choices |
| `Main.lean` | asymptotics (B = 16/ε, η = ε/16, δ = ε/32) and the two main theorems |
