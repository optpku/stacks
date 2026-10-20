module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/- Lemma 59.103.2 (1): for a morphism `f : X ⟶ Y` in `(Sch/S)_h`, the
big h and big étale direct-image functors form a commutative square. -/
@[stacks 0EW9] #check
  (AlgebraicGeometry.Scheme.HComparison.bigHEtaleCommSq :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
      Nonempty (CatCommSq
        (AlgebraicGeometry.Scheme.H.Big.morphismOfTopoi f.left).pushforward
        (AlgebraicGeometry.Scheme.HComparison.epsilon X.left).pushforward
        (AlgebraicGeometry.Scheme.HComparison.epsilon Y.left).pushforward
        (Etale.Big.morphismOfTopoi f.left).pushforward))

/- Lemma 59.103.2 (2): after composing the h-to-étale comparison with the
small-to-big étale morphisms, the resulting direct-image square commutes. -/
@[stacks 0EW9] #check
  (AlgebraicGeometry.Scheme.HComparison.hSmallEtaleCommSq :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
      Nonempty (CatCommSq
        (AlgebraicGeometry.Scheme.H.Big.morphismOfTopoi f.left).pushforward
        ((AlgebraicGeometry.Scheme.HComparison.epsilon X.left).pushforward ⋙
          (Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
        ((AlgebraicGeometry.Scheme.HComparison.epsilon Y.left).pushforward ⋙
          (Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
        (Etale.SmallToBig.smallMorphism f.left).pushforward))

end

end
