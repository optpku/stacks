/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.Algebra.PolynomialSite.LowerShriek
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point

/-!
# Derived lower shriek on polynomial algebras

Derived colimit of a degree-zero abelian presheaf on the polynomial site of a
polynomial algebra agrees with ordinary colimit placed in degree zero.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open scoped CategoryTheory

universe u q t

namespace Algebra.PolynomialSite

variable (B C : Type u) [CommRing B] [CommRing C]
variable [Algebra B C] [IsPolynomial B C]
variable [HasColimitsOfShape (PolynomialSite B C)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{t} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite B C) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- For a polynomial algebra, derived colimit restricted to degree-zero abelian presheaves is
naturally isomorphic to ordinary colimit placed in degree zero. -/
theorem lowerShriek_eq_underived :
    IsIsomorphic
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}])
      (colim ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)) :=
  sorry

/-- For an abelian presheaf on the polynomial site of a polynomial algebra, its derived colimit
is isomorphic to its ordinary colimit placed in degree zero. -/
theorem lowerShriek_eq_underived_obj
    (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj (colim.obj F)) :=
  sorry

end Algebra.PolynomialSite
