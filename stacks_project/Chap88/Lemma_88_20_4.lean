module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.RigSmooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.20.4: A rig-étale morphism of locally Noetherian formal algebraic
spaces is rig-smooth. -/
@[stacks 0GD0] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigEtale.toRigSmooth :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigEtale f], RigSmooth f)
