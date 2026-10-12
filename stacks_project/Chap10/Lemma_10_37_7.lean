/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Polynomial.IsIntegral
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.37.7: coefficients of an integral or almost integral polynomial are respectively
integral or almost integral over the base ring.

The coefficientwise conclusions are already owned by `IsIntegral.coeff` and
`IsAlmostIntegral.coeff`.

@stack 00H0
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Lemma 10.37.7 (1): if a polynomial `f ∈ K[X]` is integral over `R[X]`, then every coefficient
`αᵢ = f.coeff i` is integral over `R`. The owner abstraction is the canonical predicate
`IsIntegral R[X] f`, and the coefficientwise conclusion is exactly the derived theorem
`IsIntegral.coeff`; the textbook fraction-field case is its specialization. -/
@[stacks 00H0 "(1), integral coefficients"]
#check @IsIntegral.coeff

/- Lemma 10.37.7 (2): if a polynomial `f ∈ K[X]` is almost integral over `R[X]`, then every
coefficient `αᵢ = f.coeff i` is almost integral over `R`. Here the owner abstraction is
`IsAlmostIntegral R[X] f`, and the coefficient statement is exactly the canonical derived theorem
`IsAlmostIntegral.coeff`. -/
@[stacks 00H0 "(2), almost integral coefficients"]
#check @IsAlmostIntegral.coeff

end
