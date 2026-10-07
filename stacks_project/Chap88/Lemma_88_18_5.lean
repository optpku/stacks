module

public import stacks_project.Chap88.Definition_88_16_1
public import stacks_project.Chap88.Definition_88_18_1

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth

/-- Lemma 88.18.5: A rig-smooth morphism of locally Noetherian formal algebraic
spaces is rig-flat. -/
@[stacks 0GH3]
instance toRigFlat {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigSmooth f] : RigFlat f := sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth
