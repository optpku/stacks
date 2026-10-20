module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian

open CategoryTheory

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- The target of a finite surjective morphism from an affine scheme is affine when the
target is Noetherian. -/
theorem isAffine_target_of_isFinite_surjective
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsAffine Y]
    [IsNoetherian X] : IsAffine X := sorry

/-- The target of a finite surjective morphism from an affine scheme is affine. -/
theorem isAffine_of_isFinite_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [IsFinite f] [IsAffine X] :
    IsAffine S := sorry

end AlgebraicGeometry.Scheme
