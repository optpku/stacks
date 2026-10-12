/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.FiniteType.ClosedFiber
import StacksCheckRecall

@[expose] public section

/-!
# Closed fibers of finite fraction-field extensions

## Canonical recall

Stacks Lemma 10.119.10, tag `031F`, concerns the closed fiber over the maximal
ideal of a one-dimensional Noetherian local domain.  Its three clauses have the
canonical, reusable owners below: a chosen closed-fiber prime belongs to
`Ideal.PrimesOver`, while the finite closed fiber itself is the corresponding
subtype.  The `@[stacks 031F "(1)"]`, `@[stacks 031F "(2)"]`, and
`@[stacks 031F "(3)"]` tags are attached to those library declarations.

The former chapter-local proofs and long source-shaped declaration names were
duplicate implementations.  Downstream users should import this ReasLib leaf
and use the three owners directly.

@stack 031F
-/

@[stacks 031F "(1)"]
#check @Ideal.PrimesOver.isMaximal_of_finiteFractionRing
@[stacks 031F "(2)"]
#check @Ideal.PrimesOver.finite_of_finiteFractionRing
@[stacks 031F "(3)"]
#check @Ideal.PrimesOver.residueField_finite_of_finiteFractionRing
