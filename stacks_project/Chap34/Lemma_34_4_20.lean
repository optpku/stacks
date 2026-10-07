module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Glueing

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 34.4.20: a sheaf on the big étale site over a scheme is equivalently a compatible
system of sheaves on the small étale sites of schemes over the base, whose transitions are
invertible along étale morphisms. -/
@[stacks 021K] #check
  (AlgebraicGeometry.Scheme.Etale.SmallGlueing.fromSheaf_isEquivalence :
    ∀ S : Scheme.{u}, Functor.IsEquivalence
      (AlgebraicGeometry.Scheme.Etale.SmallGlueing.fromSheaf S))
