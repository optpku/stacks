/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.LocallyOfFinitePresentation

/-- Local finite presentation for scheme morphisms is local on the target for
the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.LocallyOfFinitePresentation : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.LocallyOfFinitePresentation
