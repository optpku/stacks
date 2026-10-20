/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Torsion

/-!
# Comparison of h and étale cohomology

The h and étale cohomology of schemes agree for locally torsion coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- Étale cohomology with locally torsion coefficients agrees with h-cohomology
of the canonical inverse image on a scheme. -/
theorem cohomology_aInverseImage {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) :
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology
          (Etale.globalEtale X)).rightDerived q).obj F)
      (((siteAbelianSectionsFunctor (hPrecoverage.toGrothendieck.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseImage X).obj F)) := sorry

/-- Bounded-below derived cohomology with locally torsion cohomology sheaves agrees
with the corresponding h-hypercohomology. -/
theorem plusCohomology_aInverseImage {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K)
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[X.smallEtaleTopology](Etale.globalEtale X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[hPrecoverage.toGrothendieck.over X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((plusAInverseImage X).obj K)))) := sorry

/-- Constant torsion coefficients give the corresponding cohomology comparison. -/
theorem cohomology_constant {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) (q : ℕ) :
    -- Local instance justification (search instability): pin the canonical small-étale sheafification proof because global weak-sheafification search times out while elaborating derived sections.
    letI : HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      @HasSheafify.isRightAdjoint _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1} _
        (PhComparison.smallEtale_hasSheafify_addCommGrp X)
    -- Local instance justification (search instability): pin the canonical h-slice sheafification proof because global weak-sheafification search times out while elaborating derived sections.
    letI : HasWeakSheafify (hPrecoverage.toGrothendieck.over X)
        AddCommGrpCat.{u + 1} :=
      @HasSheafify.isRightAdjoint _ _ (hPrecoverage.toGrothendieck.over X)
        AddCommGrpCat.{u + 1} _ (hOver_hasSheafify_addCommGrp X)
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology
          (Etale.globalEtale X)).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      (((siteAbelianSectionsFunctor (hPrecoverage.toGrothendieck.over X)
          (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf (hPrecoverage.toGrothendieck.over X)
            AddCommGrpCat.{u + 1}).obj A)) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
