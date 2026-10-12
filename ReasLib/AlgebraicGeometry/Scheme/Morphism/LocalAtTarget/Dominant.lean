/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.OpenBaseChange
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsDominant

/-- Dominance of scheme morphisms is local on the target for the fppf precoverage. -/
instance isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsDominant : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.IsDominant
