/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition.ExactFirst
public import ReasLib.CategoryTheory.Limits.ChangeOfIndex
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived colimit after presheaf inverse image

This leaf owns the comparison between derived colimit over a point and the exact inverse-image
functor on presheaves. The hypotheses retain the pointlike cosimplicial object used to identify
both derived colimits with evaluation, while the public conclusion only mentions canonical
functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe q q' t u v u' v' w

namespace CategoryTheory.DerivedColimit

section Abelian

variable {C : Type u} [Category.{v} C]
variable {C' : Type u'} [Category.{v'} C']
variable (A : Type w) [Category A] [Abelian A]
variable [HasDerivedCategory.{t} A]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ A)]
variable [HasDerivedCategory.{q'} (C'ᵒᵖ ⥤ A)]
variable (u : C' ⥤ C)
variable [HasColimitsOfShape Cᵒᵖ A] [HasColimitsOfShape C'ᵒᵖ A]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C A :
    HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory.{t} A)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C' A :
    HomotopyCategory (C'ᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory.{t} A)
  (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ A) (up ℤ))]

/-- The homotopy-level map underlying change of indexing category for derived colimits. It first
uses exactness of presheaf inverse image and then the canonical map between the two colimits. -/
@[stacks 08QA "inverse-image derived-colimit homotopy comparison"]
noncomputable def inverseImageComparisonOnHomotopy :
    (DerivedCategory.Qh :
        HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory (Cᵒᵖ ⥤ A)) ⋙
      ((Functor.presheafInverseImage u A).mapDerivedCategory ⋙
        (categoryOverPointDerivedColimit C' A :
          DerivedCategory (C'ᵒᵖ ⥤ A) ⥤ DerivedCategory A)) ⟶
    (categoryOverPointColimitToDerived C A :
      HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory A) :=
  Functor.LeftDerived.Homotopy.Composition.ExactFirst.counit
      (Functor.presheafInverseImageExact A u)
      (colim : (C'ᵒᵖ ⥤ A) ⥤ A) ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (Limits.colimitPreNat u.op) (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)

/-- The canonical natural transformation from inverse image followed by derived colimit to the
derived colimit over the original indexing category. The pointlike hypothesis is not part of the
map; it is used only to prove invertibility. -/
@[stacks 08QA "canonical inverse-image derived-colimit comparison"]
noncomputable def inverseImageComparison :
    (Functor.presheafInverseImage u A).mapDerivedCategory ⋙
        (categoryOverPointDerivedColimit C' A :
          DerivedCategory (C'ᵒᵖ ⥤ A) ⥤ DerivedCategory A) ⟶
      (categoryOverPointDerivedColimit C A :
        DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A) :=
  Functor.leftDerivedLift
    (categoryOverPointDerivedColimit C A :
      DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    ((categoryOverPointColimitToDerived C A).totalLeftDerivedCounit
      DerivedCategory.Qh (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))
    ((Functor.presheafInverseImage u A).mapDerivedCategory ⋙
      (categoryOverPointDerivedColimit C' A :
        DerivedCategory (C'ᵒᵖ ⥤ A) ⥤ DerivedCategory A))
    (inverseImageComparisonOnHomotopy A u)

/-- Precomposing the derived comparison with localization recovers its explicit homotopy-level
map. -/
@[stacks 08QA "inverse-image derived-colimit comparison equation"]
theorem inverseImageComparison_fac :
    Functor.whiskerLeft
        (DerivedCategory.Qh :
          HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory (Cᵒᵖ ⥤ A))
        (inverseImageComparison A u) ≫
      (categoryOverPointColimitToDerived C A).totalLeftDerivedCounit
        DerivedCategory.Qh (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)) =
      inverseImageComparisonOnHomotopy A u := by
  exact (categoryOverPointDerivedColimit C A).leftDerived_fac
    ((categoryOverPointColimitToDerived C A).totalLeftDerivedCounit
      DerivedCategory.Qh (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))
    ((Functor.presheafInverseImage u A).mapDerivedCategory ⋙
      categoryOverPointDerivedColimit C' A)
    (inverseImageComparisonOnHomotopy A u)

/-- A pointlike cosimplicial object before and after reindexing makes the canonical derived
colimit comparison invertible. -/
@[stacks 08QA "pointlike inverse-image comparison isomorphism"]
theorem inverseImageComparison_isIso_of_pointlike
    (Ubullet : CosimplicialObject C')
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (huUbullet : CosimplicialObject.Pointlike.HasHomSpaces
      (((CosimplicialObject.whiskering C' C).obj u).obj Ubullet)) :
    IsIso (inverseImageComparison A u) := sorry

/-- Existence of a pointlike cosimplicial object before and after reindexing makes the canonical
derived-colimit comparison invertible. -/
@[stacks 08QA "existential pointlike inverse-image comparison isomorphism"]
theorem inverseImageComparison_isIso_of_exists_pointlike
    (hUbullet : ∃ Ubullet : CosimplicialObject C',
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet ∧
        CosimplicialObject.Pointlike.HasHomSpaces
          (((CosimplicialObject.whiskering C' C).obj u).obj Ubullet)) :
    IsIso (inverseImageComparison A u) := by
  rcases hUbullet with ⟨Ubullet, hUbullet, huUbullet⟩
  exact inverseImageComparison_isIso_of_pointlike A u Ubullet hUbullet huUbullet

/-- Witness-level derived-colimit comparison: if `Ubullet` is pointlike before and after
whiskering along `u`, presheaf inverse image followed by derived colimit is isomorphic to derived
colimit on the original presheaf category. -/
@[stacks 08QA "pointlike inverse-image derived-colimit comparison"]
theorem inverseImage_isomorphic_of_pointlike
    (Ubullet : CosimplicialObject C')
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (huUbullet : CosimplicialObject.Pointlike.HasHomSpaces
      (((CosimplicialObject.whiskering C' C).obj u).obj Ubullet)) :
    IsIsomorphic
      ((Functor.presheafInverseImage u A).mapDerivedCategory ⋙
        (categoryOverPointDerivedColimit C' A :
          DerivedCategory (C'ᵒᵖ ⥤ A) ⥤ DerivedCategory A))
      (categoryOverPointDerivedColimit C A :
        DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A) := by
  letI := inverseImageComparison_isIso_of_pointlike A u Ubullet hUbullet huUbullet
  exact ⟨asIso (inverseImageComparison A u)⟩

/-- If a cosimplicial object of `C'` is pointlike both before and after whiskering along
`u : C' ⥤ C`, then derived colimit after presheaf inverse image is isomorphic to derived colimit
over `C` for coefficients in any abelian category. -/
@[stacks 08QA "coefficient-general inverse-image derived-colimit comparison"]
theorem inverseImage_isomorphic_of_exists_pointlike
    (hUbullet : ∃ Ubullet : CosimplicialObject C',
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet ∧
        CosimplicialObject.Pointlike.HasHomSpaces
          (((CosimplicialObject.whiskering C' C).obj u).obj Ubullet)) :
    IsIsomorphic
      ((Functor.presheafInverseImage u A).mapDerivedCategory ⋙
        (categoryOverPointDerivedColimit C' A :
          DerivedCategory (C'ᵒᵖ ⥤ A) ⥤ DerivedCategory A))
      (categoryOverPointDerivedColimit C A :
        DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A) := by
  rcases hUbullet with ⟨Ubullet, hUbullet, huUbullet⟩
  exact inverseImage_isomorphic_of_pointlike A u Ubullet hUbullet huUbullet

end Abelian

section SourceSpecializations

variable {C : Type u} [Category.{v} C]
variable {C' : Type u'} [Category.{v'} C']
variable (u : C' ⥤ C)

section AbelianGroups

variable [HasDerivedCategory.{t} AddCommGrpCat]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ AddCommGrpCat)]
variable [HasDerivedCategory.{q'} (C'ᵒᵖ ⥤ AddCommGrpCat)]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]
variable [HasColimitsOfShape C'ᵒᵖ AddCommGrpCat]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C AddCommGrpCat :
    HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (up ℤ) ⥤
      DerivedCategory.{t} AddCommGrpCat)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C' AddCommGrpCat :
    HomotopyCategory (C'ᵒᵖ ⥤ AddCommGrpCat) (up ℤ) ⥤
      DerivedCategory.{t} AddCommGrpCat)
  (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ AddCommGrpCat) (up ℤ))]

/-- Lemma 21.39.8 (1) (08QA): under the pointlike cosimplicial hypothesis, inverse image followed
by derived lower shriek agrees with derived lower shriek for abelian-group-valued presheaves. -/
@[stacks 08QA "abelian inverse-image derived-colimit comparison"]
theorem inverseImage_isomorphic_of_exists_pointlike_abelian
    (hUbullet : ∃ Ubullet : CosimplicialObject C',
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet ∧
        CosimplicialObject.Pointlike.HasHomSpaces
          (((CosimplicialObject.whiskering C' C).obj u).obj Ubullet)) :
    IsIsomorphic
      ((Functor.presheafInverseImage u AddCommGrpCat).mapDerivedCategory ⋙
        (categoryOverPointDerivedColimit C' AddCommGrpCat :
          DerivedCategory (C'ᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat))
      (categoryOverPointDerivedColimit C AddCommGrpCat :
        DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat) := by
  exact inverseImage_isomorphic_of_exists_pointlike AddCommGrpCat u hUbullet

end AbelianGroups

section Modules

variable {B : Type w} [Ring B]
variable [HasDerivedCategory.{t} (ModuleCat B)]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat B)]
variable [HasDerivedCategory.{q'} (C'ᵒᵖ ⥤ ModuleCat B)]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
variable [HasColimitsOfShape C'ᵒᵖ (ModuleCat B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C (ModuleCat B) :
    HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (up ℤ) ⥤ DerivedCategory.{t} (ModuleCat B))
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C' (ModuleCat B) :
    HomotopyCategory (C'ᵒᵖ ⥤ ModuleCat B) (up ℤ) ⥤ DerivedCategory.{t} (ModuleCat B))
  (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ ModuleCat B) (up ℤ))]

/-- Lemma 21.39.8 (2) (08QA): for a ring `B`, under the pointlike cosimplicial hypothesis,
inverse image followed by derived lower shriek agrees with derived lower shriek for
`B`-module-valued presheaves. -/
@[stacks 08QA "module inverse-image derived-colimit comparison"]
theorem inverseImage_isomorphic_of_exists_pointlike_module
    (hUbullet : ∃ Ubullet : CosimplicialObject C',
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet ∧
        CosimplicialObject.Pointlike.HasHomSpaces
          (((CosimplicialObject.whiskering C' C).obj u).obj Ubullet)) :
    IsIsomorphic
      ((Functor.presheafInverseImage u (ModuleCat B)).mapDerivedCategory ⋙
        (categoryOverPointDerivedColimit C' (ModuleCat B) :
          DerivedCategory (C'ᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B)))
      (categoryOverPointDerivedColimit C (ModuleCat B) :
        DerivedCategory (Cᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B)) := by
  exact inverseImage_isomorphic_of_exists_pointlike (ModuleCat B) u hUbullet

end Modules

end SourceSpecializations

end CategoryTheory.DerivedColimit
