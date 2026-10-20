module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Evaluation
public import ReasLib.AlgebraicTopology.SimplicialObject.PolynomialAugmentation

/-!
# Derived lower shriek on a polynomial simplicial resolution

Derived lower shriek on the opposite polynomial site `C_{B/A}` is computed by evaluation
on a simplicial polynomial augmentation whose underlying map is a trivial Kan fibration.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
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

/-- If `P` is a simplicial `A`-algebra with augmentation `ε` to `B`, each
term of `P` is a polynomial `A`-algebra, and the underlying simplicial-set map of `ε` is a
trivial Kan fibration, then `Lπ!(F)` is isomorphic to the cosimplicial evaluation of `F` on
`(P, ε)` in `D(Ab)`, functorially in `F` in `Ab(C)` for `C = PolynomialSite A B`. -/
theorem lowerShriek_eval_abelian (hε : I.rlp (underlyingSSetMap ε)) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), AddCommGrpCat.{u}])
      (CosimplicialObject.Evaluation.toDerived AddCommGrpCat.{u} (asCosimplicial ε hP)) := sorry

end AbelianGroups

section Modules

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- If every term of a simplicial `A`-algebra `P` is polynomial and its augmentation `ε`
to `B` is a trivial Kan fibration on underlying simplicial sets, then `Lπ!(F)` is isomorphic
to evaluation of `F` on `(P, ε)` in `D(B)`, functorially in the presheaf of `B`-modules `F`. -/
theorem lowerShriek_eval_module (hε : I.rlp (underlyingSSetMap ε)) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite A B), (ModuleCat.{u} B)])
      (CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B) (asCosimplicial ε hP)) := sorry

end Modules

end Algebra.PolynomialSite
