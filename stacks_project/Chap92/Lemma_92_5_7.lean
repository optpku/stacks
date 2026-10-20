module

public import ReasLib.RingTheory.CotangentComplex.AbelianComparison
import StacksCheckRecall

/-!
# Derived lower shriek of the structure, constant, and differential presheaves

The five comparisons record both identifications in the additive derived category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial.Site
open scoped CategoryTheory

noncomputable section

universe u q q'

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/- Lemma 92.5.7. For any ring map, derived lower shriek of the structure and constant
presheaves is the target ring in degree zero; the cotangent complex is also identified
with derived lower shriek of scalar-extended and untensored Kähler differentials. -/
@[stacks 08QK] #check (Algebra.PolynomialSite.lowerShriek_structureSheaf A B :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (structureAbelianPresheaf A B)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj
        (AddCommGrpCat.of B)))

#check (Algebra.PolynomialSite.lowerShriek_constant A B :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (constantAbelianPresheaf A B)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj
        (AddCommGrpCat.of B)))

#check (Algebra.PolynomialSite.lowerShriek_structureSheaf_constant A B :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (structureAbelianPresheaf A B)))
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (constantAbelianPresheaf A B))))

end Algebra.PolynomialSite

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

#check (Algebra.CotangentComplex.forgetDerived_lowerShriek_omega A B :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)))
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)).obj
            (omegaSheaf A B)))))

#check (Algebra.CotangentComplex.lowerShriek_omega_kaehler A B :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)).obj
            (omegaSheaf A B))))
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (kaehlerPresheaf A B))))

end Algebra.CotangentComplex
