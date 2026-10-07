module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Descent

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 29.45.7: let `f : X ⟶ S` and `g : S' ⟶ S` be morphisms of schemes. Assume `g` is a
closed immersion, `g` is bijective on points, the base change projection
`pullback.snd f g : pullback f g ⟶ S'` is a closed immersion, and either `f` is of finite type or
`g` is of finite presentation. Then `f` is a closed immersion. -/
@[stacks 0896] #check
  (AlgebraicGeometry.IsClosedImmersion.of_pullback_snd_of_bijective :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      (_ : IsClosedImmersion g)
      (_ : Function.Bijective ⇑(ConcreteCategory.hom g.base))
      (_ : IsClosedImmersion (pullback.snd f g))
      (_ : Scheme.Hom.FiniteType f ∨ Scheme.Hom.FinitePresentation g),
      IsClosedImmersion f)
