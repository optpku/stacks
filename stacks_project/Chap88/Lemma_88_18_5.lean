module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth.RigFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.18.5: A rig-smooth morphism of locally Noetherian formal algebraic
spaces is rig-flat. -/
@[stacks 0GH3] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth.toRigFlat :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigSmooth f], RigFlat f)
