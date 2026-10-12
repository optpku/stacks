/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Examples.SpecialFiber.Hypersurface

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace AlgebraicGeometry.SpecialFiberDegeneration

/-- No flat projective morphism to the complex affine line has integral special fibre
different from the projective line when all non-origin closed fibres are projective lines. -/
theorem noFlatProjectiveIntegralDegeneration :
    ¬ ∃ (X : Scheme) (f : X ⟶ SplitConicOverLine.base),
      Flat f ∧ Projective f ∧
        (∀ t : SplitConicOverLine.base,
          t ∈ closedPoints SplitConicOverLine.base → t ≠ SplitConicOverLine.origin →
            Nonempty (f.fiber t ≅ ProjectiveLine.scheme ℂ)) ∧
        ¬ Nonempty (f.fiber SplitConicOverLine.origin ≅ ProjectiveLine.scheme ℂ) ∧
        IsIntegral (f.fiber SplitConicOverLine.origin) :=
  sorry

end AlgebraicGeometry.SpecialFiberDegeneration
