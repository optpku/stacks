module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Torsion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- Étale cohomology of a locally torsion abelian sheaf agrees with ph-cohomology
of its canonical inverse image. -/
theorem cohomology_aInverseImage {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) :
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (Etale.globalEtale X)).rightDerived q).obj F)
      (((siteAbelianSectionsFunctor ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
          (Over.mk (𝟙 (Over.mk (𝟙 X))))).rightDerived q).obj
        ((aInverseImage (Over.mk (𝟙 X))).obj F)) := sorry

/-- Étale hypercohomology of a bounded-below complex with locally torsion cohomology
sheaves agrees with ph-hypercohomology of its canonical inverse image. -/
theorem plusCohomology_aInverseImage {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K)
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[X.smallEtaleTopology](Etale.globalEtale X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[(Scheme.bigPhSite X).over (Over.mk (𝟙 X))](Over.mk (𝟙 (Over.mk (𝟙 X))))).obj
          (DerivedCategory.Plus.ι.obj ((plusAInverseImage (Over.mk (𝟙 X))).obj K)))) := sorry

/-- Étale and ph-cohomology of the constant sheaf of any torsion abelian group agree. -/
theorem cohomology_constant {X : Scheme.{u}}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) (q : ℕ) :
    -- Local instance justification (defeq pin): pin the canonical weak-sheafification proof from the existing named sheafification instance because global weak-sheafification search times out even with specialized direct-projection instances.
    letI : HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      @HasSheafify.isRightAdjoint _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1} _
        (smallEtale_hasSheafify_addCommGrp X)
    -- Local instance justification (defeq pin): pin the canonical weak-sheafification proof from the existing named sheafification instance because global weak-sheafification search times out even with specialized direct-projection instances.
    letI : HasWeakSheafify ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
        AddCommGrpCat.{u + 1} :=
      @HasSheafify.isRightAdjoint _ _ ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
        AddCommGrpCat.{u + 1} _ (phSlice_hasSheafify_addCommGrp (Over.mk (𝟙 X)))
    IsIsomorphic
      (((siteAbelianSectionsFunctor X.smallEtaleTopology (Etale.globalEtale X)).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))
      (((siteAbelianSectionsFunctor ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
          (Over.mk (𝟙 (Over.mk (𝟙 X))))).rightDerived q).obj
        ((constantSheaf ((Scheme.bigPhSite X).over (Over.mk (𝟙 X)))
          AddCommGrpCat.{u + 1}).obj A)) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
