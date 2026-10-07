module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Finite
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.44.16: a finite morphism of schemes is projective. -/
@[stacks 0B3I] #check (AlgebraicGeometry.IsFinite.projective :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
    AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Projective f)
