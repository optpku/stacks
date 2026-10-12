/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived colimit and cosimplicial evaluation

This leaf owns the pointlike comparison used to compute the derived colimit of a presheaf by
evaluation on a cosimplicial object. Its coefficient-general theorem is the reusable core; the
abelian-group and module-valued statements are source-faithful specializations for Lemma 21.39.7.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped CategoryTheory Simplicial

noncomputable section

universe q q' u v w

namespace CategoryTheory.DerivedColimit

section Generic

variable {C : Type u} [Category.{v} C]
variable (A : Type w) [Category A] [Abelian A]
variable [HasColimitsOfShape Cᵒᵖ A]
variable [HasDerivedCategory.{q'} A]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ A)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C A :
    HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory.{q'} A)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))]

/-- Pointlike cosimplicial evaluation computes the derived colimit of a degree-zero presheaf with
values in any abelian category. This is the coefficient-general owner behind the abelian-group and
module specializations of Lemma 21.39.7. -/
@[stacks 08Q9 "coefficient-general derived lower-shriek evaluation"]
theorem single_isomorphic_to_evaluation
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ A) (0 : ℤ)) ⋙
        (categoryOverPointDerivedColimit C A :
          DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A))
      (CosimplicialObject.Evaluation.toDerived A Ubullet) := sorry

end Generic

section AbelianGroups

variable {C : Type u} [Category.{v} C]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]
variable [HasDerivedCategory.{q'} AddCommGrpCat]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ AddCommGrpCat)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C AddCommGrpCat :
    HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (up ℤ) ⥤ DerivedCategory.{q'} AddCommGrpCat)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (up ℤ))]

/-- Lemma 21.39.7 (08Q9), abelian-group specialization: pointlike evaluation computes the derived
lower shriek of a degree-zero abelian-group-valued presheaf. -/
@[stacks 08Q9 "abelian derived lower-shriek evaluation"]
theorem single_isomorphic_to_evaluation_abelian
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat) (0 : ℤ)) ⋙
        (categoryOverPointDerivedColimit C AddCommGrpCat :
          DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat))
      (CosimplicialObject.Evaluation.toDerived AddCommGrpCat Ubullet) := sorry

end AbelianGroups

section Modules

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [Ring B]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
variable [HasDerivedCategory.{q'} (ModuleCat B)]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C (ModuleCat B) :
    HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (up ℤ) ⥤ DerivedCategory.{q'} (ModuleCat B))
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (up ℤ))]

/-- Lemma 21.39.7 (08Q9), module specialization: pointlike evaluation computes the derived lower
shriek of a degree-zero presheaf of `B`-modules. -/
@[stacks 08Q9 "module derived lower-shriek evaluation"]
theorem single_isomorphic_to_evaluation_module
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ ModuleCat B) (0 : ℤ)) ⋙
        (categoryOverPointDerivedColimit C (ModuleCat B) :
          DerivedCategory (Cᵒᵖ ⥤ ModuleCat B) ⥤ DerivedCategory (ModuleCat B)))
      (CosimplicialObject.Evaluation.toDerived (ModuleCat B) Ubullet) := sorry

end Modules

end CategoryTheory.DerivedColimit
