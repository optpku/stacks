module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PullbackStalk
import StacksCheckRecall

/-!
# Lemma 66.29.5

The étale stalk of the pullback of a quasi-coherent module along a morphism of algebraic
spaces is the tensor product of the stalk of the original module with the étale local ring
of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

/- Lemma 66.29.5: the canonical comparison identifies the stalk of a pulled-back
quasi-coherent module with scalar extension of its stalk at the image geometric point. -/
@[stacks 05VQ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackStalkComparison_isIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (G : Y.Modules)
      [G.IsQuasicoherent] (xbar : GeometricPoint X),
      IsIso (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackStalkComparison f G xbar))
