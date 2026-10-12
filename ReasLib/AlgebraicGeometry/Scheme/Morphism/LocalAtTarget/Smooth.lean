/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFinitePresentation

/-!
# Target locality of smoothness

This file records target locality of smoothness for morphisms of schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Smooth

/-- Smoothness of scheme morphisms is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Smooth : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Smooth
