module

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.25.6: the composition of flat morphisms is flat. -/
@[stacks 01U7]
#check (AlgebraicGeometry.Flat.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.Flat f] [AlgebraicGeometry.Flat g],
    AlgebraicGeometry.Flat (f ≫ g))
