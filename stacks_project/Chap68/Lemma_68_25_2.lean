module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.UniversallyCatenary
import StacksCheckRecall

/-!
# Dimension functions on decent algebraic spaces of finite type

A dimension function on a locally Noetherian universally catenary scheme
induces a dimension function on a decent algebraic space locally of finite
type over it.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 68.25.2: If `S` is a locally Noetherian universally catenary scheme,
`δ : S → ℤ` is a dimension function, and `X` is a decent algebraic space over
`S` whose structure morphism `X ⟶ S` is locally of finite type, then
the function sending `x` to `δ` at its image in `S` plus the transcendence
degree of `x` over that image is a dimension function on `Points X`.

The general theorem below specializes with `B = ofOver (Over.mk (𝟙 S))`,
`f = SchemeRealization.toBase X`, and the dimension function on `Points B`
given by `δ ∘ (ofOver.pointsHomeomorph (Over.mk (𝟙 S))).symm`.
Scheme universal catenarity includes local Noetherianity and supplies
universal catenarity of `B` through `instUniversallyCatenary_ofOver`.
`Homeomorph.isDimensionFunction_comp_iff` transports the dimension-function
hypothesis without an additional assumption. By the definition of `Points.base`,
the resulting relative function is exactly
`x ↦ δ (Points.base x) + (residueFieldTrdegAt (SchemeRealization.toBase X) x : ℤ)`. -/
@[stacks 0ED5] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsDimensionFunction_relativeDimensionFunction :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B X : AlgebraicGeometry.AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary B] (f : X ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      (δ : AlgebraicGeometry.AlgebraicSpace.Points B → ℤ) [IsDimensionFunction δ],
      IsDimensionFunction (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ))
