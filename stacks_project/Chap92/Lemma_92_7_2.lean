/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.DerivedLowerShriek
public import ReasLib.Algebra.PolynomialTower.LowerShriek
import StacksCheckRecall

/-!
# Derived and underived lower shriek when the top algebra is polynomial

For a compatible ring tower with polynomial top algebra, the derived lower
shriek after inverse image, the derived lower shriek on the polynomial site,
and the ordinary lower shriek placed in degree zero are identified.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open scoped CategoryTheory

universe u q q' t

section PolynomialSite

variable (B C : Type u) [CommRing B] [CommRing C]
variable [Algebra B C] [IsPolynomial B C]
variable [HasColimitsOfShape (PolynomialSite B C)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{t} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite B C) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/- Lemma 92.7.2 (2). The derived lower shriek agrees with ordinary lower shriek. -/
@[stacks 08QV]
#check (Algebra.PolynomialSite.lowerShriek_eq_underived B C :
    IsIsomorphic
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}])
      (colim ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)))

#check (Algebra.PolynomialSite.lowerShriek_eq_underived_obj B C :
    ∀ (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}),
    IsIsomorphic
      ((Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj (colim.obj F)))

end PolynomialSite

section PolynomialTower

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

/- Lemma 92.7.2 (1). Inverse image along the tensor projection preserves derived lower shriek. -/
@[stacks 08QV]
#check (Algebra.PolynomialTower.lowerShriek_u3InverseImage A B C :
    IsIsomorphic
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (Algebra.PolynomialTower.forgetToOverB A B C).op AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![((PolynomialTower A B C)ᵒᵖ), AddCommGrpCat.{u}])
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]))

#check (Algebra.PolynomialTower.lowerShriek_u3InverseImage_obj A B C :
    ∀ (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}),
    IsIsomorphic
      (((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (Algebra.PolynomialTower.forgetToOverB A B C).op AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![((PolynomialTower A B C)ᵒᵖ), AddCommGrpCat.{u}]).obj F)
      (((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]).obj F))

#check (Algebra.PolynomialTower.lowerShriek_u3InverseImage_eq_underived A B C :
    ∀ (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}),
    IsIsomorphic
      ((Lπ![((PolynomialTower A B C)ᵒᵖ), AddCommGrpCat.{u}]).obj
        ((Functor.presheafInverseImage (Algebra.PolynomialTower.forgetToOverB A B C).op AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj (colim.obj F)))

end PolynomialTower
