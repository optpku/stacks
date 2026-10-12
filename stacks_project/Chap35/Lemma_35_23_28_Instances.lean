/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Syntomic

@[expose] public section

universe u

open CategoryTheory

/- Syntomicity of scheme morphisms is local on the target for the fpqc
precoverage. -/
#check
  (AlgebraicGeometry.Syntomic.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Syntomic : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
