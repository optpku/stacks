/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_13_Comparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable [HasWeakSheafify (Spec (.of ybar.K)).smallEtaleTopology (Type u)]
variable [HasWeakSheafify Y.smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u,
    (smallEtalePullback ybar.hom).op.HasLeftKanExtension P]
variable [InitiallySmall
    ((smallEtalePullback ybar.hom ⋙
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).fiber).Elements)]
variable [((smallEtalePullback ybar.hom).sheafPushforwardContinuous (Type u)
    Y.smallEtaleTopology (Spec (.of ybar.K)).smallEtaleTopology).IsRightAdjoint]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
variable [HasProducts.{u} AddCommGrpCat.{u}]
variable [(etalePullbackExact ybar.hom).obj.PreservesHomology]
variable [(etalePullbackExact (geometricFiberToX f ybar)).obj.PreservesInjectiveObjects]
variable [(etalePullbackExact (geometricFiberToX f ybar)).obj.PreservesHomology]
variable [((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
    Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u}).Additive]
variable [((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
    Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u}).PreservesHomology]
variable [PreservesFiniteLimits
    ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
      Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
        AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
    ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
      Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
        AddCommGrpCat.{u})]
variable [(siteAbelianSectionsFunctor (Spec (.of ybar.K)).smallEtaleTopology
    (globalEtale (Spec (.of ybar.K)))).PreservesHomology]
variable [HasExt.{u} (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u})]
variable [HasExt.{u} (Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- Lemma 59.91.13 (1): if `f : X ⟶ Y` is a proper morphism of schemes and `ȳ → Y` is a
geometric point, then for a torsion abelian sheaf `F` on `X_étale` the stalk
`(R^n f_* F)_ȳ` is canonically isomorphic to étale cohomology
`H^n_étale(X_ȳ, F_ȳ)` of the scheme-theoretic geometric fibre `X_ȳ = ȳ ×_Y X`. -/
@[stacks 0DDF]
theorem higherDirectImage_stalk_eq_geometricFiberCohomology
    [IsProper f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) (n : ℕ) :
    IsIso (higherDirectImageStalkToGeometricFiberCohomology f ybar F n) := sorry

variable
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong (geometricFiberToPoint f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact ybar.hom).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact (geometricFiberToX f ybar)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact ybar.hom).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact (geometricFiberToX f ybar)).obj ⋙
        abelianPushforwardAlong (geometricFiberToPoint f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong (geometricFiberToPoint f ybar) ⋙
        ((GeometricPoint.toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
          Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
            AddCommGrpCat.{u})).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}))]
    [(siteAbelianSectionsFunctor (geometricFiber f ybar).smallEtaleTopology
        (globalEtale (geometricFiber f ybar))).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}))]
    [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf (geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf (Spec (.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 59.91.13 (2): if `f : X ⟶ Y` is a proper morphism of schemes and `ȳ → Y` is a
geometric point, then for `E ∈ D⁺(X_étale)` with torsion cohomology sheaves the stalk
`(R^n f_* E)_ȳ` is canonically isomorphic to étale cohomology
`H^n_étale(X_ȳ, E|_{X_ȳ})` of the scheme-theoretic geometric fibre. -/
@[stacks 0DDF]
theorem derivedHigherDirectImage_stalk_eq_geometricFiberCohomology
    [IsProper f] (h_src : IsIso (derivedSourceComparison f ybar.hom))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E)
    (n : ℤ) :
    IsIso (derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar h_src E n) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
