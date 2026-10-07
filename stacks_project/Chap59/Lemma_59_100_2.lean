module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/-!
The printed formula for `a_Y` has an `X` subscript typo; the well-typed
composite uses `epsilon_Y` followed by `pi_Y` on the `Y` side.
-/

/- Lemma 59.100.2 (1): for a morphism `f : X ⟶ Y` over `S`, the big fppf and
big étale direct-image functors form a commutative square. -/
@[stacks 0DDM] #check
  (AlgebraicGeometry.Scheme.Fppf.bigEtaleCommSq :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
      Nonempty (CatCommSq
        (Fppf.Big.morphismOfTopoi f.left).pushforward
        (AlgebraicGeometry.StandardTopology.toFppf .etale X.left).pushforward
        (AlgebraicGeometry.StandardTopology.toFppf .etale Y.left).pushforward
        (Etale.Big.morphismOfTopoi f.left).pushforward))

/- Lemma 59.100.2 (2): after composing the fppf-to-big-étale comparison with
the small-to-big étale morphisms, the resulting direct-image square commutes. -/
@[stacks 0DDM] #check
  (AlgebraicGeometry.Scheme.Fppf.smallEtaleCommSq :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
      Nonempty (CatCommSq
        (Fppf.Big.morphismOfTopoi f.left).pushforward
        ((AlgebraicGeometry.StandardTopology.toFppf .etale X.left).pushforward ⋙
          (Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
        ((AlgebraicGeometry.StandardTopology.toFppf .etale Y.left).pushforward ⋙
          (Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
        (Etale.SmallToBig.smallMorphism f.left).pushforward))

end

end
