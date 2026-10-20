/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.StandardResolution
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.PolynomialEvaluation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek on the standard polynomial resolution

Derived lower shriek on the opposite polynomial site `C_{B/A}` is computed by
evaluation on the standard simplicial resolution of `B` over `A`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped CategoryTheory

universe u q q'

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

section AbelianGroups

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- Derived lower shriek of abelian-group presheaves on the opposite polynomial site
is naturally isomorphic to evaluation on the standard polynomial resolution. -/
@[stacks 08PT]
theorem lowerShriek_standard_eval_abelian :
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), AddCommGrpCat.{u}])
      (CosimplicialObject.Evaluation.toDerived AddCommGrpCat.{u}
        (standardCosimplicial A B)) :=
  sorry

/-- Derived lower shriek of an abelian-group presheaf is isomorphic in `D(Ab)` to
its evaluation on the standard polynomial resolution. -/
theorem lowerShriek_standard_eval_abelian_obj
    (F : (PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj F)
      ((CosimplicialObject.Evaluation.toDerived AddCommGrpCat.{u}
          (standardCosimplicial A B)).obj F) :=
  sorry

end AbelianGroups

section Modules

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- Derived lower shriek of presheaves of `B`-modules on the opposite polynomial
site is naturally isomorphic to evaluation on the standard polynomial resolution. -/
@[stacks 08PT]
theorem lowerShriek_standard_eval_module :
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), (ModuleCat.{u} B)])
      (CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B)
        (standardCosimplicial A B)) :=
  sorry

/-- Derived lower shriek of a presheaf of `B`-modules is isomorphic in `D(B)` to
its evaluation on the standard polynomial resolution. -/
theorem lowerShriek_standard_eval_module_obj
    (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj F)
      ((CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B)
          (standardCosimplicial A B)).obj F) :=
  sorry

end Modules

end Algebra.PolynomialSite
