/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.143.12

@stack 00UA
-/

-- Declarations for this item will be appended below by the statement pipeline.

section

open Polynomial

variable (n m : ℕ)

/- Example 10.143.12: the textbook generic factorization map
`ℤ[a₁, …, a_{n+m}] → ℤ[b₁, …, bₙ, c₁, …, cₘ]`, localized away from the Sylvester determinant
or equivalently the resultant of the two generic monic factors, is exactly the canonical owner
`Polynomial.UniversalCoprimeFactorizationRing`. Its étaleness is the upstream instance below. The
source positivity hypotheses `n, m ≥ 1` are redundant for this canonical statement and are
therefore omitted from the public surface. -/
@[stacks 00UA]
#check (inferInstance :
  Algebra.Etale (MvPolynomial (Fin (n + m)) ℤ)
    (UniversalCoprimeFactorizationRing n m rfl (MonicDegreeEq.freeMonic ℤ (n + m))))

end
