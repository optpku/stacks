module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.BaseChange
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.Cancellation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Rig-étaleness of the relative diagonal
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- The relative diagonal of a rig-étale morphism of locally Noetherian formal
algebraic spaces is rig-étale. -/
instance diagonal {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [RigEtale f] : RigEtale (pullback.diagonal f) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
