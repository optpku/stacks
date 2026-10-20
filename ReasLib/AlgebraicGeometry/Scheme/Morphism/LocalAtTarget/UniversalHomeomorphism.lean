/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Surjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyInjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyOpen

/-!
# Fpqc locality of universal homeomorphisms

Universal homeomorphisms of schemes form a morphism property local at the target
for the fpqc precoverage.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.UniversalHomeomorphism

/-- Universal homeomorphisms of schemes are local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.UniversalHomeomorphism : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.UniversalHomeomorphism
