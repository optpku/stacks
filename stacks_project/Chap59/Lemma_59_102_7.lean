/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PhComparison
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

/- Lemma 59.102.7 (1): for a scheme `X` and a torsion abelian sheaf `F` on `X_étale`,
étale cohomology `H^q(X_étale, F)` agrees with ph-cohomology `H^q_ph(X, a_X⁻¹ F)`. -/
@[stacks 0DE6]
#check (AlgebraicGeometry.Scheme.PhComparison.cohomology_aInverseImage :
    ∀ {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ),
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology
          (AlgebraicGeometry.Scheme.Etale.globalEtale X)).rightDerived q).obj F)
      (((siteAbelianSectionsFunctor ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
          (Over.mk (𝟙 (Over.mk (𝟙 X))))).rightDerived q).obj
        ((aInverseImage (Over.mk (𝟙 X))).obj F)))

/- Lemma 59.102.7 (2): for a scheme `X` and `K ∈ D⁺(X_étale)` with torsion cohomology
sheaves, étale hypercohomology `H^q(X_étale, K)` agrees with ph-hypercohomology
`H^q_ph(X, a_X⁻¹ K)`. -/
@[stacks 0DE6]
#check (AlgebraicGeometry.Scheme.PhComparison.plusCohomology_aInverseImage :
    ∀ {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K)
    (q : ℤ),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[X.smallEtaleTopology](AlgebraicGeometry.Scheme.Etale.globalEtale X)).obj
          (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[(Scheme.bigPhSite X).over (Over.mk (𝟙 X))](Over.mk (𝟙 (Over.mk (𝟙 X))))).obj
          (DerivedCategory.Plus.ι.obj ((plusAInverseImage (Over.mk (𝟙 X))).obj K)))))

/- Lemma 59.102.7 (3): for a scheme `X` and a torsion abelian group `A`, étale
cohomology of the constant sheaf with value `A` agrees with ph-cohomology of
the constant sheaf with value `A`. -/
@[stacks 0DE6]
#check (AlgebraicGeometry.Scheme.PhComparison.cohomology_constant :
    ∀ {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) (q : ℕ),
    -- Local instance justification (defeq pin): pin the canonical weak-sheafification proof from the existing named sheafification instance because global weak-sheafification search times out even with specialized direct-projection instances.
    letI : HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      @HasSheafify.isRightAdjoint _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1} _
        (AlgebraicGeometry.Scheme.PhComparison.smallEtale_hasSheafify_addCommGrp X)
    -- Local instance justification (defeq pin): pin the canonical weak-sheafification proof from the existing named sheafification instance because global weak-sheafification search times out even with specialized direct-projection instances.
    letI : HasWeakSheafify ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
        AddCommGrpCat.{u + 1} :=
      @HasSheafify.isRightAdjoint _ _ ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
        AddCommGrpCat.{u + 1} _
        (AlgebraicGeometry.Scheme.PhComparison.phSlice_hasSheafify_addCommGrp (Over.mk (𝟙 X)))
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology
          (AlgebraicGeometry.Scheme.Etale.globalEtale X)).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      (((siteAbelianSectionsFunctor ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
          (Over.mk (𝟙 (Over.mk (𝟙 X))))).rightDerived q).obj
        ((constantSheaf ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
          AddCommGrpCat.{u + 1}).obj A)))

end

end
