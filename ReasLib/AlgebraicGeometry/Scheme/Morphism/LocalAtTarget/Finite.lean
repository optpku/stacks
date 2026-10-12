/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFiniteType

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsFinite

/-- Finite morphisms of schemes are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsFinite : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsFinite
