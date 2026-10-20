/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.30.2: for a finite-type scheme morphism, the function assigning
to each target point the Krull dimension of its fibre is preserved by arbitrary
base change. -/
@[stacks 05F8] #check
  (AlgebraicGeometry.Scheme.Hom.fiberDimension_baseChange :
    ∀ {Y X Y' X' : Scheme.{u}} (f : X ⟶ Y) [FiniteType f]
      (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → f'.fiberDimension = f.fiberDimension ∘ g)

end AlgebraicGeometry.Scheme.Hom
