module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleDerived
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedSections

/-!
# Comparison of étale and pro-étale derived global sections

Bounded-below derived global sections and abelian sheaf cohomology agree
after inverse image from the small étale site to the small pro-étale site.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}]
variable [Functor.HasRightDerivedFunctor
    ((siteAbelianSectionsFunctor X.smallEtaleTopology (Etale.globalEtale X)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))]
variable [Functor.HasRightDerivedFunctor
    ((siteAbelianSectionsFunctor (ProEt.topology X) (ProEt.globalProEt X)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}))]

/-- Bounded-below derived global sections of abelian étale sheaves on a scheme
are isomorphic to pro-étale derived global sections of their derived inverse image. -/
theorem etaleToProEt_plusPullback_globalSections_isIsomorphic
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((siteAbelianSectionsBoundedBelowDerived
          X.smallEtaleTopology (Etale.globalEtale X)).obj K)
      ((siteAbelianSectionsBoundedBelowDerived
          (ProEt.topology X) (ProEt.globalProEt X)).obj
        ((etaleToProEt_plusPullback X).obj K)) :=
  sorry

/-- In every nonnegative degree, the cohomology of an abelian étale sheaf on a scheme
is isomorphic to the pro-étale cohomology of its inverse-image sheaf. -/
theorem etaleToProEtPullback_cohomology_isIsomorphic
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    IsIsomorphic
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((siteAbelianSectionsBoundedBelowDerived
            X.smallEtaleTopology (Etale.globalEtale X)).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)))
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
        ((siteAbelianSectionsBoundedBelowDerived
            (ProEt.topology X) (ProEt.globalProEt X)).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) (0 : ℤ)).obj
            ((etaleToProEtPullback X AddCommGrpCat.{u + 1}).obj F)))) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
