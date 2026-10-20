module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Glueing
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Proposition 88.26.1
Restriction along a proper morphism that is an isomorphism over the open
complement and along the completion gives a bijection onto compatible pairs.
-/
@[stacks 0GI3] #check
  (AlgebraicGeometry.AlgebraicSpace.completionAlong.GlueingHom.ofHom_bijective :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} [IsLocallyNoetherian X]
      (T : Closeds (Points X)) (f : X' ⟶ X)
      [Proper f] [IsIso (openInverseImageTo f (openComplementι X T))]
      (W : AlgebraicSpace S),
      Function.Bijective
        (AlgebraicGeometry.AlgebraicSpace.completionAlong.GlueingHom.ofHom f T W))
