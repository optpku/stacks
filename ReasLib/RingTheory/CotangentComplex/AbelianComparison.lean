/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.AbelianPresheaves
public import ReasLib.RingTheory.CotangentComplex.PolynomialSite
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat

/-!
# Additive derived comparisons on the polynomial site

Derived lower shriek identifies the source and constant additive presheaves with the
target ring, and compares scalar-extended and untensored Kähler differentials.
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

/-- The derived lower shriek of the additive source-ring presheaf is the target ring in degree zero. -/
@[stacks 08QK]
theorem lowerShriek_structureSheaf :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (structureAbelianPresheaf A B)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj
        (AddCommGrpCat.of B)) :=
  sorry

/-- The derived lower shriek of the constant target-ring presheaf is that ring in degree zero. -/
@[stacks 08QK]
theorem lowerShriek_constant :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (constantAbelianPresheaf A B)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj
        (AddCommGrpCat.of B)) :=
  sorry

/-- The additive source-ring and constant target-ring presheaves have isomorphic
derived lower shrieks. -/
theorem lowerShriek_structureSheaf_constant :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (structureAbelianPresheaf A B)))
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (constantAbelianPresheaf A B))) :=
  sorry

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

/-- Forgetting the module structure identifies the cotangent complex with derived lower
shriek of scalar-extended differentials in the additive derived category. -/
@[stacks 08QK]
theorem forgetDerived_lowerShriek_omega :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)))
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)).obj
            (omegaSheaf A B)))) :=
  sorry

/-- Derived lower shriek identifies scalar-extended and untensored Kähler differentials
in the additive derived category. -/
@[stacks 08QK]
theorem lowerShriek_omega_kaehler :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)).obj
            (omegaSheaf A B))))
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (kaehlerPresheaf A B))) :=
  sorry

end Algebra.CotangentComplex
