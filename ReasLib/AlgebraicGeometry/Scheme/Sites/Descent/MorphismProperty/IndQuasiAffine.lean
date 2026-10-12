/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty

@[expose] public section

universe u

namespace AlgebraicGeometry.IndQuasiAffineHom

/-- Every scheme descent datum over an fpqc covering whose component structure morphisms
are ind-quasi-affine is effective. -/
theorem satisfiesDescentFpqc :
    CategoryTheory.MorphismProperty.SatisfiesDescent
      (@AlgebraicGeometry.IndQuasiAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) .fpqc := sorry

end AlgebraicGeometry.IndQuasiAffineHom
