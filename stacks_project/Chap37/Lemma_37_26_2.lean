/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.26.2: the locus where the fibres of a scheme morphism are geometrically
reduced is preserved by arbitrary base change. -/
@[stacks 0576] #check
  (AlgebraicGeometry.Scheme.Hom.geometricallyReducedFiberLocus_baseChange :
    ∀ {Y X Y' X' : AlgebraicGeometry.Scheme.{u}},
      (f : X ⟶ Y) → (g : Y' ⟶ Y) → (g' : X' ⟶ X) → (f' : X' ⟶ Y') →
        (sq : IsPullback g' f' f g) →
          f'.geometricallyReducedFiberLocus =
            g ⁻¹' f.geometricallyReducedFiberLocus)
