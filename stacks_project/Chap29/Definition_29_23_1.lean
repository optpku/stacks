module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 29.23.1 (1): a morphism of schemes is open when its map on underlying topological
spaces is open. -/
@[stacks 01U0] #check
  (AlgebraicGeometry.topologically (@IsOpenMap) :
    CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})

/- Definition 29.23.1 (2): a morphism of schemes is universally open when every base change is
open on underlying topological spaces. -/
@[stacks 01U0] #check
  (AlgebraicGeometry.UniversallyOpen :
    ∀ {X S : Scheme.{u}}, (X ⟶ S) → Prop)

#check
  (AlgebraicGeometry.universallyOpen_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      UniversallyOpen f ↔ (topologically @IsOpenMap).universally f)
