module

import StacksCheckRecall
import stacks_project.Chap76.Theorem_76_8_1_Equivalence

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Theorem 76.8.1: if `f : X ⟶ Y` is an integral, universally injective, and
surjective morphism of algebraic spaces over a scheme `S`, the functor
`V ↦ V_X = X ×_Y V` defines an equivalence of categories
`Y_spaces,étale ⥤ X_spaces,étale`. -/
@[stacks 05ZH] #check
  (spacesEtalePullback.isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsIntegralHom f] [UniversallyInjective f] [Surjective f],
      (spacesEtalePullback f).IsEquivalence)
