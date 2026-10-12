/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
