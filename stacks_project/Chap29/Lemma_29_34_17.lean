module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials.Conormal

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.34.17

Let `i : Z ⟶ X` be an immersion of schemes over `S`. If `Z` is smooth over `S`, then the
canonical conormal sequence is short exact.
-/
@[stacks 06AA] #check
  (AlgebraicGeometry.Smooth.conormalDifferentials_shortExact.{u} :
    ∀ {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
      (f : X ⟶ S) [Smooth (i ≫ f)],
      (Scheme.Hom.Conormal.Differentials.complex i f).ShortExact)
