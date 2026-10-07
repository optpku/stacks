module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.EtaleComparison

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/- Lemma 59.102.2 (1): for a morphism `f : X ⟶ Y` in `(Sch/S)ₚₕ`, the
comparison between big `ph` and big étale sheaves is a commutative square of
functors. -/
@[stacks 0DDX] #check (AlgebraicGeometry.Scheme.PhComparison.bigPhEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
    Nonempty (CatCommSq (Ph.Big.morphismOfTopoi f.left).pushforward
      (PhComparison.standardComparison .etale X.left).pushforward (PhComparison.standardComparison .etale Y.left).pushforward
      (Etale.Big.morphismOfTopoi f.left).pushforward))

/- Lemma 59.102.2 (2): after composing the big comparison with the canonical
big-to-small étale direct images, the resulting square is commutative; its
vertical functors are the source's `a_X` and `a_Y`. -/
@[stacks 0DDX] #check (AlgebraicGeometry.Scheme.PhComparison.phSmallEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
    Nonempty (CatCommSq (Ph.Big.morphismOfTopoi f.left).pushforward
      ((PhComparison.standardComparison .etale X.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
      ((PhComparison.standardComparison .etale Y.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
      (Etale.SmallToBig.smallMorphism f.left).pushforward))

end

end
