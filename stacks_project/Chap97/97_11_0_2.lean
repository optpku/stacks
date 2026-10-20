module

public import stacks_project.Chap97.«97_11_0_2_RestrictionOfScalars»
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry Opposite

/- 97.11.0.2: For morphisms `X ⟶ Z ⟶ B` of algebraic spaces over a scheme `S`,
the restriction-of-scalars functor `Res_{Z/B}(X) : (Sch/S)ᵒᵖ ⟶ Sets` sends a
scheme `T` over `S` to the set of pairs `(a, b)` with `a : T ⟶ B` and
`b : T ×_{a,B} Z ⟶ X` a morphism over `Z`. -/
@[stacks 05YA]
#check (AlgebraicGeometry.AlgebraicSpace.restrictionOfScalars :
  ∀ {S : Scheme.{u}} {X Z B : AlgebraicSpace S},
    (X ⟶ Z) → (Z ⟶ B) → ((Over S)ᵒᵖ ⥤ Type (u + 1)))
