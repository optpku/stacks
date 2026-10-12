/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_20_2
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed

/-!
# Prime divisors on algebraic spaces

A prime divisor on a decent algebraic space is classified by an irreducible
closed subset of `Points X` of coheight one, via the reduced induced integral
closed subspace of Lemma 72.4.7.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]

/-- A prime divisor on an algebraic space is the canonical integral closed
subspace of coheight one associated to an irreducible closed subset of
`Points X`. -/
structure PrimeDivisor where
  /-- The irreducible closed support in `Points X`. -/
  support : IrreducibleCloseds (Points X)
  /-- The irreducible closed support has coheight one. -/
  coheight_eq_one : Order.coheight support = 1

namespace PrimeDivisor

/-- Construct a prime divisor from an irreducible closed subset of coheight
one. -/
def ofSupport (T : IrreducibleCloseds (Points X))
    (h_coheight : Order.coheight T = 1) : PrimeDivisor X where
  support := T
  coheight_eq_one := h_coheight

/-- The support recovered from `ofSupport` is the original irreducible closed
set. -/
theorem ofSupport_support (T : IrreducibleCloseds (Points X))
    (h_coheight : Order.coheight T = 1) :
    (ofSupport X T h_coheight).support = T :=
  sorry

/-- The canonical integral closed subspace associated to a prime divisor. -/
def subspace (Z : PrimeDivisor X) : ClosedSubspace X :=
  ClosedSubspace.ofIrreducibleClosed Z.support

/-- The closed subspace of a prime divisor is the reduced induced structure on
its support. -/
theorem subspace_eq_ofIrreducibleClosed (Z : PrimeDivisor X) :
    Z.subspace = ClosedSubspace.ofIrreducibleClosed Z.support :=
  sorry

/-- Construct a prime divisor from an integral closed subspace of coheight one,
using the canonical reduced induced structure on its point-set. -/
def ofSubspace (Z : ClosedSubspace X) [IsIntegral Z.X]
    (h_coheight : Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1) :
    PrimeDivisor X :=
  ofSupport X (ClosedSubspace.irreducibleClosed Z) h_coheight

/-- The support of `ofSubspace Z` is the irreducible closed point-set of `Z`. -/
theorem ofSubspace_support (Z : ClosedSubspace X) [IsIntegral Z.X]
    (h_coheight : Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1) :
    (ofSubspace X Z h_coheight).support = ClosedSubspace.irreducibleClosed Z :=
  sorry

/-- The underlying algebraic space of a prime divisor. -/
abbrev space (Z : PrimeDivisor X) : AlgebraicSpace S :=
  Z.subspace.X

/-- The closed-immersion inclusion of a prime divisor. -/
abbrev ι (Z : PrimeDivisor X) : Z.space ⟶ X :=
  Z.subspace.ι

/-- The image of a prime divisor in `Points X`. -/
abbrev pointsSet (Z : PrimeDivisor X) : Set (Points X) :=
  Z.subspace.pointsSet

/-- The underlying point-set of a prime divisor is its irreducible closed
support. -/
theorem pointsSet_eq_support (Z : PrimeDivisor X) :
    Z.pointsSet = (Z.support : Set (Points X)) :=
  sorry

/-- The inclusion of a prime divisor is a closed immersion. -/
theorem isClosedImmersion_ι (Z : PrimeDivisor X) : IsClosedImmersion Z.ι :=
  sorry

/-- The underlying algebraic space of a prime divisor is integral. -/
theorem isIntegral_space (Z : PrimeDivisor X) : IsIntegral Z.space :=
  sorry

/-- A prime divisor is a closed immersion of an integral algebraic space whose
support is irreducible of coheight one. -/
theorem spec (Z : PrimeDivisor X) :
    IsClosedImmersion Z.ι ∧ IsIntegral Z.space ∧
      _root_.IsIrreducible Z.pointsSet ∧ Order.coheight Z.support = 1 :=
  sorry

/-- The generic point of the support of a prime divisor, as a point of `X`. -/
abbrev genericPoint (Z : PrimeDivisor X) : Points X :=
  Z.support.isIrreducible.genericPoint

/-- The generic point of a prime divisor has codimension one on `X`. -/
theorem localRingDimAt_genericPoint (Z : PrimeDivisor X) :
    localRingDimAt Z.genericPoint = 1 :=
  sorry

end PrimeDivisor

end AlgebraicGeometry.AlgebraicSpace
