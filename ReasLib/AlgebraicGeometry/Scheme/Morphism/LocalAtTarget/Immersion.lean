/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.ClosedImmersion

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsImmersion

/-- Immersions of schemes are local on the target for the fppf precoverage. -/
instance isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsImmersion : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.IsImmersion
