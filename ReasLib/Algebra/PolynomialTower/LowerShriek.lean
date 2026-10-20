/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialTower
public import ReasLib.Algebra.PolynomialSite.DerivedLowerShriek
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage

/-!
# Derived lower shriek along polynomial towers

For a polynomial top algebra, tensor base change compares derived colimits on
the polynomial tower site and the polynomial site over the middle ring.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open scoped CategoryTheory

universe u q q' t

namespace Algebra.PolynomialTower

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsPolynomial B C]

variable [HasColimitsOfShape (PolynomialSite B C)ᵒᵖ AddCommGrpCat.{u}]
variable [HasColimitsOfShape ((PolynomialTower A B C)ᵒᵖ)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{t} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q'} (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite B C) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived ((PolynomialTower A B C)ᵒᵖ) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- For a polynomial top algebra, inverse image along tensor base change followed by derived
colimit agrees on degree-zero abelian presheaves with derived colimit on the polynomial site. -/
theorem lowerShriek_u3InverseImage :
    IsIsomorphic
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (Algebra.PolynomialTower.forgetToOverB A B C).op AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![((PolynomialTower A B C)ᵒᵖ), AddCommGrpCat.{u}])
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]) :=
  sorry

/-- For an abelian presheaf on the polynomial site of a polynomial top algebra, derived colimit
after inverse image along tensor base change is isomorphic to its original derived colimit. -/
theorem lowerShriek_u3InverseImage_obj
    (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (Algebra.PolynomialTower.forgetToOverB A B C).op AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![((PolynomialTower A B C)ᵒᵖ), AddCommGrpCat.{u}]).obj F)
      (((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]).obj F) :=
  sorry

/-- For a polynomial top algebra, the derived colimit of the inverse image of an abelian
presheaf along tensor base change is isomorphic to its ordinary colimit placed in degree zero. -/
theorem lowerShriek_u3InverseImage_eq_underived
    (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((Lπ![((PolynomialTower A B C)ᵒᵖ), AddCommGrpCat.{u}]).obj
        ((Functor.presheafInverseImage (Algebra.PolynomialTower.forgetToOverB A B C).op AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj (colim.obj F)) :=
  sorry

end Algebra.PolynomialTower
