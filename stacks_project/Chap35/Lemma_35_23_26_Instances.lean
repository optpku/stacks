/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiFinite

universe u

open CategoryTheory

#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)

#check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Scheme.Hom.QuasiFinite :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
