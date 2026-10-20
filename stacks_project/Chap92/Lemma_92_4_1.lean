module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.PolynomialEvaluation
import StacksCheckRecall

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

/- Lemma 92.4.1 (1). Derived lower shriek is computed by evaluation on
the polynomial simplicial augmentation, functorially in presheaves of abelian groups. -/
@[stacks 08PS] #check (Algebra.PolynomialSite.lowerShriek_eval_abelian ε hP :
  I.rlp (underlyingSSetMap ε) →
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), AddCommGrpCat.{u}])
      (CosimplicialObject.Evaluation.toDerived AddCommGrpCat.{u} (asCosimplicial ε hP)))

end AbelianGroups

section Modules

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/- Lemma 92.4.1 (2). Derived lower shriek is computed by evaluation on
the polynomial simplicial augmentation, functorially in presheaves of B-modules. -/
@[stacks 08PS] #check (Algebra.PolynomialSite.lowerShriek_eval_module ε hP :
  I.rlp (underlyingSSetMap ε) →
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), (ModuleCat.{u} B)])
      (CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B) (asCosimplicial ε hP)))

end Modules

end Algebra.PolynomialSite
