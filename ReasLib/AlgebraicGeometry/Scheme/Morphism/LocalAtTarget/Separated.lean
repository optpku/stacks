/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyClosed

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsSeparated

/-- Separatedness of scheme morphisms is local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsSeparated : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsSeparated
