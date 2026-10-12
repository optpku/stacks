/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.KrullDimension.Fiber.Valuation

@[expose] public section

/-!
# Valuation-ring special-fiber recall

The canonical objects are the closed and generic `Ideal.Fiber` constructions.
Their componentwise dimension comparison, equidimensionality, and global
dimension consequence are owned by the valuation-ring fiber leaf in ReasLib.

@stack 00QK
-/

/- Lemma 10.125.9, tag 00QK: for an injective finite-type domain algebra over a valuation ring,
the prime spectrum of `Ideal.Fiber (maximalIdeal R) S` is equidimensional. -/
@[stacks 00QK "equidimensional valuation-ring special fiber"]
#check @ValuationRing.SpecialFiber.equidimensional_of_finiteType

/- Companion API, tag 00QK: for a nontrivial closed fiber, its Krull dimension equals that of
`Ideal.Fiber (⊥ : Ideal R) S`. -/
@[stacks 00QK "dimension of a valuation-ring special fiber"]
#check @ValuationRing.SpecialFiber.ringKrullDim_eq_genericFiber_of_finiteType
