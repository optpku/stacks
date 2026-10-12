/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.25.15: let `f : X ⟶ Y` be a flat morphism of schemes. If `V ⊆ Y` is a
retrocompact scheme-theoretically dense open, then `f ⁻¹ᵁ V` is scheme-theoretically dense
in `X`. -/
@[stacks 081H] #check
  (AlgebraicGeometry.schemeTheoreticallyDense_preimage_of_flat_of_isRetrocompact :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
      (V : Y.Opens),
      IsRetrocompact (V : Set Y) →
        AlgebraicGeometry.schemeTheoreticallyDense V →
          AlgebraicGeometry.schemeTheoreticallyDense (f ⁻¹ᵁ V))
