/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.52.3: for a locally finite-type morphism `f : X ⟶ S` to a universally catenary
scheme and a dimension function `δ : S → ℤ`, the function
`x ↦ δ (f x) + (f.residueFieldTrdegAt x : ℤ)` is a dimension function on `X`. -/
@[stacks 02JW] #check
  (AlgebraicGeometry.Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
      (δ : S → ℤ) [IsDimensionFunction δ],
      IsDimensionFunction (f.relativeDimensionFunction δ))
