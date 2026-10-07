module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StalkPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 38.2.2: for a commutative square of schemes with étale horizontal maps, the
induced morphism after base change by `S'.fromSpecStalk s'` is étale. -/
@[stacks 05H2] #check
  (AlgebraicGeometry.Scheme.Hom.stalkPullbackMap_etale :
    ∀ {X' S' X S : Scheme.{u}}
      (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
      [Etale i] [Etale g] (sq : CommSq i f' f g) (s' : S'),
      Etale (Scheme.Hom.stalkPullbackMap f' i g f sq s'))
