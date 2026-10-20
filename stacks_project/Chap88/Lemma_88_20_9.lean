module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion.RigSmooth
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

/- Lemma 88.20.9: For a closed immersion of locally Noetherian formal algebraic
spaces, rig-smoothness, rig-étaleness, and the universal affine étale chart test
by surjections whose kernel cotangent is annihilated by an ideal of definition
are equivalent. -/
@[stacks 0GD4] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.tfae_rigSmooth :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
      [ClosedImmersion f],
      List.TFAE [RigSmooth f, RigEtale f,
        AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.etaleAffine_kernelCotangent f])
