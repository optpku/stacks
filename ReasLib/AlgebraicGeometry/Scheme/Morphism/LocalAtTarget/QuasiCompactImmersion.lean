/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.OpenImmersion

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.QuasiCompactImmersion

/-- Quasi-compact immersions of schemes are local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.QuasiCompact ⊓ @AlgebraicGeometry.IsImmersion) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.QuasiCompactImmersion
