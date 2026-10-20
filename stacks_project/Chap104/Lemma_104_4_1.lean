/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import stacks_project.Chap104.Lemma_104_3_1_Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 104.4.1

On an algebraic stack, derived abelian lower shriek of the constant integer
sheaf along the lisse-étale and flat-fppf inclusions is the constant integer
sheaf in the unbounded derived category.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/-- The canonical comparison from the constant integer sheaf on the lisse-étale
site to the inverse image of the constant integer sheaf on the associated étale
site. -/
def lisseEtaleInverseImage_constantInteger_hom :
    constantIntegerSheaf (lisseEtaleTopology X) ⟶
      ((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
          (lisseEtaleTopology X) X.etaleTopology).obj
        (constantIntegerSheaf X.etaleTopology) :=
  ((sheafificationAdjunction (lisseEtaleTopology X) AddCommGrpCat.{z}).homEquiv
      ((const (lisseEtaleSite X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{z} ℤ)))
      (((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
          (lisseEtaleTopology X) X.etaleTopology).obj
        (constantIntegerSheaf X.etaleTopology))).symm
    ((constCompWhiskeringLeftIso (lisseEtaleSite X)ᵒᵖ
          (lisseEtaleInclusion X).op).inv.app
        (AddCommGrpCat.of (ULift.{z} ℤ)) ≫
      whiskerLeft (lisseEtaleInclusion X).op
        ((sheafificationAdjunction X.etaleTopology AddCommGrpCat.{z}).unit.app
          ((const (X.total)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{z} ℤ)))))

/-- The canonical comparison from the constant integer sheaf on the flat-fppf
site to the inverse image of the constant integer sheaf on the inherited fppf
site. -/
def flatFppfInverseImage_constantInteger_hom :
    constantIntegerSheaf (flatFppfTopology X) ⟶
      ((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
          (flatFppfTopology X) (inheritedFppfTopology X)).obj
        (constantIntegerSheaf (inheritedFppfTopology X)) :=
  ((sheafificationAdjunction (flatFppfTopology X) AddCommGrpCat.{z}).homEquiv
      ((const (flatFppfSite X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{z} ℤ)))
      (((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
          (flatFppfTopology X) (inheritedFppfTopology X)).obj
        (constantIntegerSheaf (inheritedFppfTopology X)))).symm
    ((constCompWhiskeringLeftIso (flatFppfSite X)ᵒᵖ
          (flatFppfInclusion X).op).inv.app
        (AddCommGrpCat.of (ULift.{z} ℤ)) ≫
      whiskerLeft (flatFppfInclusion X).op
        ((sheafificationAdjunction (inheritedFppfTopology X)
            AddCommGrpCat.{z}).unit.app
          ((const (X.total)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{z} ℤ)))))

/-- The canonical derived comparison `Lg_! ℤ ⟶ ℤ` along the lisse-étale
inclusion of an algebraic stack. -/
def lisseEtaleAbelianLowerShriekDerived_constantInteger :
    (lisseEtaleAbelianLowerShriekDerived X).obj
        ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (constantIntegerSheaf (lisseEtaleTopology X))) ⟶
      (DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (constantIntegerSheaf X.etaleTopology) :=
  ((lisseEtaleAbelianLowerShriekDerived.adjunction X).homEquiv
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (constantIntegerSheaf (lisseEtaleTopology X)))
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (constantIntegerSheaf X.etaleTopology))).symm
    ((DerivedCategory.singleFunctor _ (0 : ℤ)).map
        (lisseEtaleInverseImage_constantInteger_hom X) ≫
      ((siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
            (lisseEtaleTopology X) X.etaleTopology
            (lisseEtaleInclusion X)).obj.mapDerivedCategorySingleFunctor
          (0 : ℤ)).inv.app
        (constantIntegerSheaf X.etaleTopology))

/-- The canonical derived comparison `Lg_! ℤ ⟶ ℤ` along the flat-fppf
inclusion of an algebraic stack. -/
def flatFppfAbelianLowerShriekDerived_constantInteger :
    (flatFppfAbelianLowerShriekDerived X).obj
        ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (constantIntegerSheaf (flatFppfTopology X))) ⟶
      (DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (constantIntegerSheaf (inheritedFppfTopology X)) :=
  ((flatFppfAbelianLowerShriekDerived.adjunction X).homEquiv
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (constantIntegerSheaf (flatFppfTopology X)))
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (constantIntegerSheaf (inheritedFppfTopology X)))).symm
    ((DerivedCategory.singleFunctor _ (0 : ℤ)).map
        (flatFppfInverseImage_constantInteger_hom X) ≫
      ((siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
            (flatFppfTopology X) (inheritedFppfTopology X)
            (flatFppfInclusion X)).obj.mapDerivedCategorySingleFunctor
          (0 : ℤ)).inv.app
        (constantIntegerSheaf (inheritedFppfTopology X)))

/-- Lemma 104.4.1 (1): for an algebraic stack `X`, `Lg_! ℤ = ℤ` in the
unbounded derived category of abelian sheaves, where `Lg_!` is the lisse-étale
comparison of Lemma 104.3.1 part (1). -/
@[stacks 0H0Z]
instance lisseEtaleAbelianLowerShriekDerived_constantInteger.instIsIso :
    IsIso (lisseEtaleAbelianLowerShriekDerived_constantInteger X) := sorry

/-- Lemma 104.4.1 (2): for an algebraic stack `X`, `Lg_! ℤ = ℤ` in the
unbounded derived category of abelian sheaves, where `Lg_!` is the flat-fppf
comparison of Lemma 104.3.1 part (3). -/
@[stacks 0H0Z]
instance flatFppfAbelianLowerShriekDerived_constantInteger.instIsIso :
    IsIso (flatFppfAbelianLowerShriekDerived_constantInteger X) := sorry

end AlgebraicGeometry.AlgebraicStack
