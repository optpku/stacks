/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Fppf and étale cohomology comparison

Étale cohomology and bounded-below hypercohomology agree with fppf cohomology
after the canonical inverse image, including for constant abelian sheaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Étale cohomology of an abelian sheaf agrees with fppf cohomology of its
canonical inverse image. -/
theorem cohomology_aInverseImage {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (Etale.globalEtale X)).rightDerived q).obj F)
      (((siteAbelianSectionsFunctor (fppfTopology.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseAb X).obj F)) := sorry

/-- Étale hypercohomology of a bounded-below complex of abelian sheaves agrees
with fppf hypercohomology of its canonical inverse image. -/
theorem plusCohomology_aInverseImage {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[X.smallEtaleTopology](Etale.globalEtale X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[fppfTopology.over X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((aInverseAbPlus X).obj K)))) := sorry

/-- The canonical inverse image of a constant abelian sheaf on the small étale
site is isomorphic to the constant abelian sheaf on the big fppf slice. -/
theorem aInverseAb_obj_constantSheaf {X : Scheme.{u}} (A : AddCommGrpCat.{u + 1}) :
    IsIsomorphic
      ((aInverseAb X).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      ((constantSheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}).obj A) := sorry

/-- Étale and fppf cohomology of the constant sheaf of any abelian group agree. -/
theorem cohomology_constant {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (Etale.globalEtale X)).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      (((siteAbelianSectionsFunctor (fppfTopology.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}).obj A)) := sorry

end AlgebraicGeometry.Scheme.FppfEtale

end

end
