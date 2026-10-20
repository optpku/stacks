module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.CardinalType
import StacksCheckRecall

/-!
# Remark 95.8.3

The discussion of the stack of finite type algebraic spaces still produces a
stack over `(Sch/S)_fppf` if one restricts to algebraic spaces `X / U` that are
locally of finite type and whose inverse image of every affine open of `U` is
covered by countably many affines. Independently, a bound `κ` on generators of
ring extensions and on affine covers of inverse images of affines produces a
stack `Spaces_κ` over `(Sch/S)_fppf`, with `Scheme.{u}` large enough for
`κ : Cardinal.{u}`. Both stacks admit essentially surjective full subcategories
whose projections are stacks with `u`-small fibers. The same-universe convention
uses `S : Scheme.{u}`, `κ : Cardinal.{u}`, ring carriers in `Type u`, and
`u`-small atlas indices to express the required size of the scheme universe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 95.8.3: the stack over `(Sch/S)_fppf` of algebraic spaces
`X / U` that are locally of finite type and whose inverse image of every affine
open of `U` is covered by countably many affines. -/
@[stacks 04UF]
#check (AlgebraicGeometry.AlgebraicSpace.CountablyAffineLocallyOfFiniteType.stack :
  ∀ S : Scheme.{u}, StackOver (Scheme.fppfTopology.over S))

#check (AlgebraicGeometry.AlgebraicSpace.CountablyAffineLocallyOfFiniteType.stack_p :
  ∀ S : Scheme.{u},
    (CountablyAffineLocallyOfFiniteType.stack S).p =
      CountablyAffineLocallyOfFiniteType.forget S)

#check (AlgebraicGeometry.AlgebraicSpace.CountablyAffineLocallyOfFiniteType.exists_smallSubcategory :
  ∀ S : Scheme.{u},
    ∃ P : ObjectProperty (CountablyAffineLocallyOfFiniteType.stack S).total,
      P.ι.EssSurj ∧
        IsStack.OnSite (Scheme.fppfTopology.over S)
          (P.ι ⋙ (CountablyAffineLocallyOfFiniteType.stack S).p) ∧
        ∀ U : Over S,
          Small.{u} ((P.ι ⋙ (CountablyAffineLocallyOfFiniteType.stack S).p).Fiber U))

#check (AlgebraicGeometry.AlgebraicSpace.OfCardinalType.stack :
  ∀ (κ : Cardinal.{u}) (S : Scheme.{u}),
    StackOver (Scheme.fppfTopology.over S))

#check (AlgebraicGeometry.AlgebraicSpace.OfCardinalType.stack_p :
  ∀ (κ : Cardinal.{u}) (S : Scheme.{u}),
    (OfCardinalType.stack κ S).p = OfCardinalType.forget κ S)

#check (AlgebraicGeometry.AlgebraicSpace.OfCardinalType.exists_smallSubcategory :
  ∀ (κ : Cardinal.{u}) (S : Scheme.{u}),
    ∃ P : ObjectProperty (OfCardinalType.stack κ S).total,
      P.ι.EssSurj ∧
        IsStack.OnSite (Scheme.fppfTopology.over S)
          (P.ι ⋙ (OfCardinalType.stack κ S).p) ∧
        ∀ U : Over S, Small.{u} ((P.ι ⋙ (OfCardinalType.stack κ S).p).Fiber U))

end AlgebraicGeometry.AlgebraicSpace
