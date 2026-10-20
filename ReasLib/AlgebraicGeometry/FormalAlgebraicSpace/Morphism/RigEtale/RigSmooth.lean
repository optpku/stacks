module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth
public import ReasLib.RingTheory.AdicCompletion.RigEtale.RigSmooth

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- A rig-étale morphism of locally Noetherian formal algebraic spaces is rig-smooth. -/
instance toRigSmooth {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigEtale f] : RigSmooth f := sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
