/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Evaluation
public import stacks_project.Chap92.Lemma_92_4_2_Resolution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek on the standard polynomial resolution

Lemma 92.4.2 identifies `Lπ!` on the opposite polynomial site `C_{B/A}` with evaluation
on the standard simplicial resolution of `B` over `A`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
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

/-- Lemma 92.4.2 (1). If `ε : P_• ⟶ B` is the standard resolution of `B` over `A` and
`π` is as in 92.4.0.1, then `Lπ!(F)` is isomorphic to the cosimplicial evaluation of
`F` on `(P_•, ε)` in `D(Ab)`, functorially in `F` in `Ab(C)` for
`C = PolynomialSite A B`. -/
@[stacks 08PT]
theorem lowerShriek_standard_eval_abelian :
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), AddCommGrpCat.{u}])
      (CosimplicialObject.Evaluation.toDerived AddCommGrpCat.{u}
        (standardCosimplicial A B)) :=
  sorry

/-- Objectwise form of the abelian identification `Lπ!(F) ≅ F(P_•, ε)` in `D(Ab)` for
the standard resolution. -/
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

/-- Lemma 92.4.2 (2). If `ε : P_• ⟶ B` is the standard resolution of `B` over `A` and
`π` is as in 92.4.0.1, then `Lπ!(F)` is isomorphic to the cosimplicial evaluation of
`F` on `(P_•, ε)` in `D(B)`, functorially in `F` in `Mod(underline B)`, identified
here with `(PolynomialSite A B)ᵒᵖ ⥤ ModuleCat B`. -/
@[stacks 08PT]
theorem lowerShriek_standard_eval_module :
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), (ModuleCat.{u} B)])
      (CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B)
        (standardCosimplicial A B)) :=
  sorry

/-- Objectwise form of the module identification `Lπ!(F) ≅ F(P_•, ε)` in `D(B)` for
the standard resolution. -/
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
