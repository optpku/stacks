/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.QuasiCompact

/-- Quasi-compactness of scheme morphisms descends along flat surjective morphisms
in pullback squares with affine bases. -/
theorem affineDescendsAlongFlat :
    AffineDescendsAlong
      (@AlgebraicGeometry.QuasiCompact : MorphismProperty AlgebraicGeometry.Scheme.{u})
      (@AlgebraicGeometry.Flat : MorphismProperty AlgebraicGeometry.Scheme.{u}) := sorry

/-- Quasi-compactness of scheme morphisms is local on the target for the fpqc
precoverage. -/
theorem isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.QuasiCompact : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.QuasiCompact
