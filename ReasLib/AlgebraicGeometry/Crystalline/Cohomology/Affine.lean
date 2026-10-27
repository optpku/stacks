/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.LeftExact

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- A locally quasi-coherent module sheaf on the small crystalline site has vanishing
positive-degree cohomology over every object whose thickening or source is affine. -/
theorem higherCohomology_isZero_of_affine
    {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    (F : CrystallineModuleSheaf.CrisModuleSheaf
      B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
    (hF : CrystallineModuleSheaf.IsCrisSheaf p B.toSpec B.prime_nilpotent F)
    (h_quasiCoherent : CrystallineModuleSheaf.CrisModuleSheaf.IsLocallyQuasiCoherent F)
    (A : smallCrystallineSite
      B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
    (h_affine : IsAffine A.obj.1.thickening ∨ IsAffine A.obj.1.source.left)
    (q : ℕ) (hq : 0 < q) :
    IsZero
      ((hF.abelianSheafULift p B.toSpec B.prime_nilpotent).cohomologyOverObject.{u + 1, u + 1} A q) := sorry

end AlgebraicGeometry.Scheme.Crystalline
