module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

@[expose] public section

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

/-- The ambient scheme of a universal first-order thickening is formally unramified
over the base whenever its closed part is formally unramified over the base. -/
instance formallyUnramified {X : Scheme.{u}} (T : Thickening.Over X)
    [IsUniversalFirstOrder T] [AlgebraicGeometry.FormallyUnramified T.left.hom] :
    AlgebraicGeometry.FormallyUnramified T.right.hom := sorry

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
