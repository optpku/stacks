module

import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import StacksCheckRecall

universe u

open CategoryTheory

namespace AlgebraicGeometry

/- Lemma 29.9.2: The composition of surjective morphisms is surjective. -/
@[stacks 01S0] #check (@AlgebraicGeometry.instSurjectiveCompScheme :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g],
    Surjective (f ≫ g))

end AlgebraicGeometry
