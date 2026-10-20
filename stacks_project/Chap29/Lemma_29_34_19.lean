/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 29.34.19: in a commutative diagram `X ⟶ Y ⟶ S`, if the first morphism is
surjective and smooth, the composite is smooth, and the second morphism is locally of finite
presentation, then the second morphism is smooth. This is equivalent to the source formulation
with a morphism `p : X ⟶ S` and an equality identifying the composite with `p`. -/
@[stacks 02K5] #check
  (AlgebraicGeometry.Smooth.of_comp_surjective :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f],
      Smooth f → Smooth (f ≫ q) → LocallyOfFinitePresentation q → Smooth q)

end AlgebraicGeometry
