module

public import Mathlib.LinearAlgebra.InvariantBasisNumber
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.15.8

@stack 0FJ7
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [Semiring R] [InvariantBasisNumber R]

/- Lemma 10.15.8, `core/canonical` layer for the invariant-basis-number owner abstraction:
over a semiring with invariant basis number, if `R^{\oplus n}` and `R^{\oplus m}` are isomorphic
as `R`-modules, then `n = m`.

This is exactly the canonical derived theorem `eq_of_fin_equiv` for the owner class
`InvariantBasisNumber`; it specializes to the source-text case of a nonzero commutative ring by
typeclass inference. -/
@[stacks 0FJ7]
#check @eq_of_fin_equiv

end
