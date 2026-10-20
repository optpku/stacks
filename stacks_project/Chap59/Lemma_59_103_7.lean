/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.CohomologyComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

/- Lemma 59.103.7
   For a scheme X, étale and h cohomology agree for locally torsion coefficients. -/
@[stacks 0EWH] #check
  (AlgebraicGeometry.Scheme.HComparison.cohomology_aInverseImage :
    ∀ {X : Scheme.{u}}
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      F.IsLocallyTorsion → (q : ℕ) →
      IsIsomorphic
        (((siteAbelianSectionsFunctor X.smallEtaleTopology
            (AlgebraicGeometry.Scheme.Etale.globalEtale X)).rightDerived q).obj F)
        (((siteAbelianSectionsFunctor (hPrecoverage.toGrothendieck.over X)
            (Over.mk (𝟙 X))).rightDerived q).obj
          ((AlgebraicGeometry.Scheme.HComparison.aInverseImage X).obj F)))

#check
  (AlgebraicGeometry.Scheme.HComparison.plusCohomology_aInverseImage :
    ∀ {X : Scheme.{u}}
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K → (q : ℤ) →
      IsIsomorphic
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
          ((RΓ[X.smallEtaleTopology](AlgebraicGeometry.Scheme.Etale.globalEtale X)).obj
            (DerivedCategory.Plus.ι.obj K)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
          ((RΓ[hPrecoverage.toGrothendieck.over X](Over.mk (𝟙 X))).obj
            (DerivedCategory.Plus.ι.obj
              ((AlgebraicGeometry.Scheme.HComparison.plusAInverseImage X).obj K)))))

#check
  (AlgebraicGeometry.Scheme.HComparison.cohomology_constant :
    ∀ {X : Scheme.{u}} (A : AddCommGrpCat.{u + 1})
      (hA : AddMonoid.IsTorsion A) (q : ℕ),
      -- Local instance justification (search instability): pin the canonical small-étale sheafification proof because global weak-sheafification search times out while elaborating derived sections.
      letI : HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
        @HasSheafify.isRightAdjoint _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1} _
          (PhComparison.smallEtale_hasSheafify_addCommGrp X)
      -- Local instance justification (search instability): pin the canonical h-slice sheafification proof because global weak-sheafification search times out while elaborating derived sections.
      letI : HasWeakSheafify (hPrecoverage.toGrothendieck.over X)
          AddCommGrpCat.{u + 1} :=
        @HasSheafify.isRightAdjoint _ _ (hPrecoverage.toGrothendieck.over X)
          AddCommGrpCat.{u + 1} _ (HComparison.hOver_hasSheafify_addCommGrp X)
      IsIsomorphic
        (((siteAbelianSectionsFunctor X.smallEtaleTopology
            (AlgebraicGeometry.Scheme.Etale.globalEtale X)).rightDerived q).obj
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
        (((siteAbelianSectionsFunctor (hPrecoverage.toGrothendieck.over X)
            (Over.mk (𝟙 X))).rightDerived q).obj
          ((constantSheaf (hPrecoverage.toGrothendieck.over X)
            AddCommGrpCat.{u + 1}).obj A)))

end

end
