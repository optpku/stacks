/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.BoundedBelow
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open CategoryTheory.Functor.RightDerived.Bounded
open CategoryTheory.ExactFunctor.Derived.Plus

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Etale

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    ((siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}))]

/-- Underived comparison `Γ(X_étale, F) ⟶ Γ(Z_étale, p⁻¹ F)` at the identity étale objects,
as the adjunction unit followed by `sectionsIso` and `globalEtalePullbackIso`. -/
def etaleAbelianSectionsRestrictAlong {Z X : Scheme.{u}} (p : Z ⟶ X) :
    siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X) ⟶
      etaleAbelianSheafPullback p ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z) where
  app F :=
    (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)).map
      (((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
          X.smallEtaleTopology Z.smallEtaleTopology).unit.app F) ≫
    (SiteAbelianSectionsDerived.sectionsIso (smallEtalePullback p) (globalEtale X) :
          abelianPushforwardAlong p ⋙
              siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X) ≅
            siteAbelianSectionsFunctor Z.smallEtaleTopology
              ((smallEtalePullback p).obj (globalEtale X))).hom.app
      ((etaleAbelianSheafPullback p).obj F) ≫
    ((sheafSections Z.smallEtaleTopology AddCommGrpCat.{u}).map
        (op (globalEtalePullbackIso p).inv)).app
      ((etaleAbelianSheafPullback p).obj F)
  naturality := sorry

/-- Evaluating `etaleAbelianSectionsRestrictAlong` recovers the adjunction-unit comparison,
the continuous pushforward sections identification, and restriction along
`globalEtalePullbackIso`. -/
theorem etaleAbelianSectionsRestrictAlong_eq {Z X : Scheme.{u}} (p : Z ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSectionsRestrictAlong p).app F =
      (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)).map
        (((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
            X.smallEtaleTopology Z.smallEtaleTopology).unit.app F) ≫
      (SiteAbelianSectionsDerived.sectionsIso (smallEtalePullback p) (globalEtale X) :
            abelianPushforwardAlong p ⋙
                siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X) ≅
              siteAbelianSectionsFunctor Z.smallEtaleTopology
                ((smallEtalePullback p).obj (globalEtale X))).hom.app
        ((etaleAbelianSheafPullback p).obj F) ≫
      ((sheafSections Z.smallEtaleTopology AddCommGrpCat.{u}).map
          (op (globalEtalePullbackIso p).inv)).app
        ((etaleAbelianSheafPullback p).obj F) := rfl

/-- Canonical restriction `H^q_étale(X, E) ⟶ H^q_étale(Z, p⁻¹ E)` on `D⁺`, as homology of the
bounded-below derived sections comparison of `etaleAbelianSectionsRestrictAlong`, the composition
comparison `R(p⁻¹ ⋙ Γ(Z)) ⟶ R(p⁻¹) ⋙ RΓ(Z)`, and the exact-functor identification of `R(p⁻¹)`. -/
noncomputable def derivedEtaleCohomologyRestrict {Z X : Scheme.{u}} (p : Z ⟶ X)
    [(etaleAbelianSheafPullback p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etaleAbelianSheafPullback p ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).obj
      ((functor
          (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X))).obj E) ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).obj
        ((functor
            (siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z))).obj
          ((etaleDerivedInverseImage p).obj E)) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).map
    ((map (etaleAbelianSectionsRestrictAlong p)).app E ≫
      (Composition.BoundedBelow.comparison (etaleAbelianSheafPullback p)
          (siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z))).app E ≫
      (Functor.whiskerRight
          (rightDerivedIso (etalePullbackExact p)).hom
          (functor
            (siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)))).app E)

/-- `derivedEtaleCohomologyRestrict` is homology of the bounded-below derived sections
restriction, the composition comparison, and the exact inverse-image identification. -/
theorem derivedEtaleCohomologyRestrict_eq {Z X : Scheme.{u}} (p : Z ⟶ X)
    [(etaleAbelianSheafPullback p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etaleAbelianSheafPullback p ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (q : ℤ) :
    derivedEtaleCohomologyRestrict p E q =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).map
        ((map (etaleAbelianSectionsRestrictAlong p)).app E ≫
          (Composition.BoundedBelow.comparison (etaleAbelianSheafPullback p)
              (siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z))).app E ≫
          (Functor.whiskerRight
              (rightDerivedIso (etalePullbackExact p)).hom
              (functor
                (siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)))).app E) :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end

end
