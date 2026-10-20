/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- The étale cohomology presheaf on `Y.Etale` obtained by pulling back the degree-`p`
cohomology presheaf along `smallEtalePullback f`. -/
def etalePullbackCohomologyPresheaf
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (p : ℕ) :
    Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (presheafInverseImage (smallEtalePullback f) AddCommGrpCat.{u}).obj
    ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology p).obj F)

/-- Evaluation of `etalePullbackCohomologyPresheaf` at `V` is the cohomology of `F` on
the base-change object `(smallEtalePullback f).obj V`. -/
theorem etalePullbackCohomologyPresheaf_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (p : ℕ) (V : Y.Etale) :
    (etalePullbackCohomologyPresheaf f F p).obj (op V) =
      (F.cohomologyPresheaf p).obj (op ((smallEtalePullback f).obj V)) :=
  rfl

/-- The degree-`p` higher direct image along `f` is the sheafification of the pulled-back
étale cohomology presheaf. -/
theorem higherDirectImage_sheafification
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (p : ℕ) :
    IsIsomorphic
      (Sheaf.higherDirectImage (smallEtalePullback f) F p)
      ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        (etalePullbackCohomologyPresheaf f F p)) := sorry

variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- The derived restriction map on sections induced by a morphism of base-change objects. -/
def etalePullbackDerivedCohomologyMap {V W : Y.Etale} (g : V ⟶ W) :
    siteAbelianSectionsDerived X.smallEtaleTopology
        ((smallEtalePullback f).obj W) ⟶
      siteAbelianSectionsDerived X.smallEtaleTopology
        ((smallEtalePullback f).obj V) :=
  Functor.rightDerivedNatTrans
    (siteAbelianSectionsDerived X.smallEtaleTopology ((smallEtalePullback f).obj W))
    (siteAbelianSectionsDerived X.smallEtaleTopology ((smallEtalePullback f).obj V))
    (RightDerived.Cochain.unit
      (siteAbelianSectionsFunctor X.smallEtaleTopology ((smallEtalePullback f).obj W)))
    (RightDerived.Cochain.unit
      (siteAbelianSectionsFunctor X.smallEtaleTopology ((smallEtalePullback f).obj V)))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).map
          ((smallEtalePullback f).map g).op)
        (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The derived restriction map attached to an identity morphism is the identity map. -/
theorem etalePullbackDerivedCohomologyMap_id (V : Y.Etale) :
    etalePullbackDerivedCohomologyMap f (𝟙 V) = 𝟙 _ := sorry

/-- Derived restriction maps compose contravariantly with morphisms of base-change objects. -/
theorem etalePullbackDerivedCohomologyMap_comp {U V W : Y.Etale}
    (g : U ⟶ V) (h : V ⟶ W) :
    etalePullbackDerivedCohomologyMap f (g ≫ h) =
      etalePullbackDerivedCohomologyMap f h ≫ etalePullbackDerivedCohomologyMap f g := sorry

/-- The derived étale cohomology presheaf on `Y.Etale` in the integer degree `q`, with values
given by derived sections of `K` on each base-change object. -/
def etalePullbackDerivedCohomologyPresheaf
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (q : ℤ) :
    Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V :=
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
      ((siteAbelianSectionsDerived X.smallEtaleTopology
          ((smallEtalePullback f).obj V.unop)).obj K)
  map {V W} g :=
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map
      ((etalePullbackDerivedCohomologyMap f g.unop).app K)
  map_id := by
    intro V
    simpa using congrArg
      (fun τ => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map (τ.app K))
      (etalePullbackDerivedCohomologyMap_id f V.unop)
  map_comp := by
    intro V W Z g h
    simpa using congrArg
      (fun τ => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map (τ.app K))
      (etalePullbackDerivedCohomologyMap_comp f h.unop g.unop)

/-- Evaluation of `etalePullbackDerivedCohomologyPresheaf` at `V` is the degree-`q` homology of
derived sections of `K` on `(smallEtalePullback f).obj V`. -/
theorem etalePullbackDerivedCohomologyPresheaf_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (q : ℤ)
    (V : Y.Etale) :
    (etalePullbackDerivedCohomologyPresheaf f K q).obj (op V) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
        ((siteAbelianSectionsDerived X.smallEtaleTopology
            ((smallEtalePullback f).obj V)).obj K) :=
  rfl

/-- The degree-`q` higher direct image of an arbitrary unbounded derived object is the
sheafification of the presheaf of degree-`q` derived étale cohomology on base changes. -/
theorem derivedHigherDirectImage_sheafification
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) q).obj
        ((RightDerived.Cochain.functor
          ((smallEtalePullback f).sheafPushforwardContinuous
            AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology)).obj K))
      ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        (etalePullbackDerivedCohomologyPresheaf f K q)) := sorry

end AlgebraicGeometry.Scheme
