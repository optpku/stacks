/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyConnected

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.28.2: the locus where the fibres of a scheme morphism are geometrically
connected is preserved by arbitrary base change. -/
@[stacks 055E] #check
  (AlgebraicGeometry.Scheme.Hom.geometricallyConnectedFiberLocus_baseChange :
    ∀ {Y X Y' X' : AlgebraicGeometry.Scheme.{u}},
      (f : X ⟶ Y) → (g : Y' ⟶ Y) → (g' : X' ⟶ X) → (f' : X' ⟶ Y') →
        (sq : IsPullback g' f' f g) →
          f'.geometricallyConnectedFiberLocus =
            g ⁻¹' f.geometricallyConnectedFiberLocus)
