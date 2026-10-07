module

public import stacks_project.Chap88.Definition_88_18_1
public import stacks_project.Chap88.Definition_88_20_1

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- Lemma 88.20.4: A rig-étale morphism of locally Noetherian formal algebraic
spaces is rig-smooth. -/
@[stacks 0GD0]
instance toRigSmooth {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigEtale f] : RigSmooth f := sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
