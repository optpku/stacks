module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified

/-!
# Universal first-order thickenings of formally unramified morphisms

The ambient morphism of a universal first-order thickening of a formally
unramified morphism of algebraic spaces is formally unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- If `i : Z ⟶ Z'` is a universal first-order thickening over `X` via
`f : Z' ⟶ X` and `i ≫ f` is formally unramified, then `f` is formally
unramified. -/
theorem formallyUnramified {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') (f : Z' ⟶ X) [IsUniversalFirstOrder i f]
    [FormallyUnramified (i ≫ f)] : FormallyUnramified f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
