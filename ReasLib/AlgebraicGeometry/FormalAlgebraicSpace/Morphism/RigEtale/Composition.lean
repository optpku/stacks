module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale

/-!
# Composition of rig-étale morphisms

The composition of rig-étale morphisms of locally Noetherian formal algebraic
spaces is again rig-étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- The composition of rig-étale morphisms of locally Noetherian formal algebraic
spaces over a scheme is rig-étale. -/
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigEtale f] [RigEtale g] : RigEtale (f ≫ g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
