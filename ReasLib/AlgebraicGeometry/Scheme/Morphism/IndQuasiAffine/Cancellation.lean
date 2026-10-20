/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.LocalAtTarget

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IndQuasiAffineHom

/-- Ind-quasi-affine scheme morphisms can be cancelled from an arbitrary
postcomposition. -/
instance hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty
      (@IndQuasiAffineHom : MorphismProperty Scheme.{u}) ⊤ := sorry

/-- If a composite of scheme morphisms is ind-quasi-affine, then its first factor is
ind-quasi-affine. -/
theorem of_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : IndQuasiAffineHom (f ≫ g)) : IndQuasiAffineHom f := sorry

end AlgebraicGeometry.IndQuasiAffineHom
