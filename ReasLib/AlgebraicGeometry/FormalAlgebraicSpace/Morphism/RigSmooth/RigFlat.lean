module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigFlat

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth

/-- A rig-smooth morphism of locally Noetherian formal algebraic spaces over a
scheme is rig-flat. -/
@[stacks 0GH3]
instance toRigFlat {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigSmooth f] : RigFlat f := sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth
