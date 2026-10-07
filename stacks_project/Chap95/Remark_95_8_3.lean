module

public import stacks_project.Chap95.Remark_95_8_3_CardinalType

/-!
# Remark 95.8.3

The discussion of the stack of finite type algebraic spaces still produces a
stack over `(Sch/S)_fppf` if one restricts to algebraic spaces `X / U` that are
locally of finite type and whose inverse image of every affine open of `U` is
covered by countably many affines. Independently, a bound `κ` on generators of
ring extensions and on affine covers of inverse images of affines produces a
stack `Spaces_κ` over `(Sch/S)_fppf`, with `Scheme.{u}` large enough for
`κ : Cardinal.{u}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 95.8.3 (1): the stack over `(Sch/S)_fppf` of algebraic spaces
`X / U` that are locally of finite type and whose inverse image of every affine
open of `U` is covered by countably many affines. -/
@[stacks 04UF]
abbrev countablyAffineSpaces (S : Scheme.{u}) :
    StackOver (Scheme.fppfTopology.over S) :=
  CountablyAffineLocallyOfFiniteType.stack S

/-- The projection of `countablyAffineSpaces S` is the forgetful functor to
`(Sch/S)_fppf`. -/
theorem countablyAffineSpaces_p (S : Scheme.{u}) :
    (countablyAffineSpaces S).p =
      CountablyAffineLocallyOfFiniteType.forget S :=
  sorry

/-- Remark 95.8.3 (2): the stack `Spaces_κ` of morphisms of `κ`-type over
`(Sch/S)_fppf`, for a cardinal `κ` with `Scheme.{u}` large enough. -/
@[stacks 04UF]
abbrev cardinalTypeSpaces (κ : Cardinal.{u}) (S : Scheme.{u}) :
    StackOver (Scheme.fppfTopology.over S) :=
  OfCardinalType.stack κ S

/-- The projection of `cardinalTypeSpaces κ S` is the forgetful functor to
`(Sch/S)_fppf`. -/
theorem cardinalTypeSpaces_p (κ : Cardinal.{u}) (S : Scheme.{u}) :
    (cardinalTypeSpaces κ S).p = OfCardinalType.forget κ S :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
