module

public import Erdos824.Main

public section

/-!
# Proof of the Palomar statement

The existing proof supplies the same explicitly conditional result as the
independent Challenge. The squarefree strengthening and the WD argument are
not part of this declaration.
-/

/-- The conditional lower bound for coprime equal-σ pairs, proved by the
finite counting argument and its asymptotic parameter estimates. -/
theorem Palomar824.main_result (H : Erdos824.SmoothSuccessorHypWeak) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      (x : ℝ) ^ (2 - ε) < (Erdos824.h x : ℝ) := by
  exact Erdos824.erdos824_of_smoothSuccessorWeak H
