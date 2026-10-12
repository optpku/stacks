/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Cancellation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IndQuasiAffineHom

/-- Ind-quasi-affine scheme morphisms are stable under arbitrary base change. -/
instance stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IndQuasiAffineHom : MorphismProperty Scheme.{u}) := sorry

end AlgebraicGeometry.IndQuasiAffineHom
