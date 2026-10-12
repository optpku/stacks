/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Evaluation
public import stacks_project.Chap92.Lemma_92_4_1_Evaluation
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek on a polynomial simplicial resolution

Lemma 92.4.1 identifies `Lπ!` on the opposite polynomial site `C_{B/A}` with evaluation
on a simplicial polynomial augmentation whose underlying map is a trivial Kan fibration.
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

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
variable (hP : ∀ n, IsPolynomial A (P.obj n))

section AbelianGroups

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- Lemma 92.4.1 (1). If `P` is a simplicial `A`-algebra with augmentation `ε` to `B`, each
term of `P` is a polynomial `A`-algebra, and the underlying simplicial-set map of `ε` is a
trivial Kan fibration, then `Lπ!(F)` is isomorphic to the cosimplicial evaluation of `F` on
`(P, ε)` in `D(Ab)`, functorially in `F` in `Ab(C)` for `C = PolynomialSite A B`. -/
@[stacks 08PS]
theorem lowerShriek_eval_abelian (hε : I.rlp (underlyingSSetMap ε)) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), AddCommGrpCat.{u}])
      (CosimplicialObject.Evaluation.toDerived AddCommGrpCat.{u} (asCosimplicial ε hP)) :=
  sorry

/-- Objectwise form of the abelian identification `Lπ!(F) ≅ F(P, ε)` in `D(Ab)`. -/
theorem lowerShriek_eval_abelian_obj (hε : I.rlp (underlyingSSetMap ε))
    (F : (PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj F)
      ((CosimplicialObject.Evaluation.toDerived AddCommGrpCat.{u}
          (asCosimplicial ε hP)).obj F) :=
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

/-- Lemma 92.4.1 (2). Under the same hypotheses as (1), `Lπ!(F)` is isomorphic to the
cosimplicial evaluation of `F` on `(P, ε)` in `D(B)`, functorially in `F` in
`Mod(underline B)`, identified here with `(PolynomialSite A B)ᵒᵖ ⥤ ModuleCat B`. -/
@[stacks 08PS]
theorem lowerShriek_eval_module (hε : I.rlp (underlyingSSetMap ε)) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), (ModuleCat.{u} B)])
      (CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B) (asCosimplicial ε hP)) :=
  sorry

/-- Objectwise form of the module identification `Lπ!(F) ≅ F(P, ε)` in `D(B)`. -/
theorem lowerShriek_eval_module_obj (hε : I.rlp (underlyingSSetMap ε))
    (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj F)
      ((CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B)
          (asCosimplicial ε hP)).obj F) :=
  sorry

end Modules

end Algebra.PolynomialSite
