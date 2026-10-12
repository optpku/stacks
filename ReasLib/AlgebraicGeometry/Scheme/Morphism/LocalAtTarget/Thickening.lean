/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Surjective

/-!
# Fpqc-locality of thickenings

Thickenings and first-order thickenings of schemes are local on the target for the fpqc
precoverage.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsThickening

/-- Being a thickening is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsThickening : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsThickening

namespace AlgebraicGeometry.IsFirstOrderThickening

/-- Being a first-order thickening is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsFirstOrderThickening :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsFirstOrderThickening
