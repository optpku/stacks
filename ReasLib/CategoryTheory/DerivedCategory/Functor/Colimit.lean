/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import ReasLib.CategoryTheory.Functor.Derived.Model

@[expose] public section

/-!
# Derived Colimits of Diagrams

This module supplies the canonical homotopy-to-derived and total-left-derived functors induced by
the colimit functor on an arbitrary diagram category.  It is independent of a geometric
interpretation of the indexing category, so specializations to presheaves or categories over a
point can remain thin compatibility layers.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.Functor

/-- The colimit functor on `A`-valued diagrams indexed by `C` is additive. -/
instance colim_additive
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasColimitsOfShape C A] :
    (colim : (C ⥤ A) ⥤ A).Additive := sorry

/-- The homotopy-to-derived functor induced by colimit on `A`-valued `C`-diagrams. -/
abbrev colimitToDerived
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasColimitsOfShape C A] :
    HomotopyCategory (C ⥤ A) (up ℤ) ⥤ DerivedCategory A :=
  Functor.Homotopy.toDerived (colim : (C ⥤ A) ⥤ A)

/-- The total left derived functor of colimit on `A`-valued `C`-diagrams. -/
abbrev derivedColimit
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (C ⥤ A)] [HasColimitsOfShape C A]
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived C A)
      (HomotopyCategory.quasiIso (C ⥤ A) (up ℤ))] :
    DerivedCategory (C ⥤ A) ⥤ DerivedCategory A :=
  (colimitToDerived C A).totalLeftDerived
    (DerivedCategory.Qh :
      HomotopyCategory (C ⥤ A) (up ℤ) ⥤ DerivedCategory (C ⥤ A))
    (HomotopyCategory.quasiIso (C ⥤ A) (up ℤ))

/-- An explicit model for the total left-derived colimit.  The functor and its counit are concrete
fields; the universal-property law is carried separately so downstream constructions can fix a
model without selecting data from `HasLeftDerivedFunctor`. -/
@[stacks 05SA "explicit derived colimit model"]
abbrev ColimitModel
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (C ⥤ A)] [HasColimitsOfShape C A] :=
  LeftDerived.Model
    (colimitToDerived C A)
    (DerivedCategory.Qh :
      HomotopyCategory (C ⥤ A) (up ℤ) ⥤ DerivedCategory (C ⥤ A))
    (HomotopyCategory.quasiIso (C ⥤ A) (up ℤ))

/-- The canonical explicit colimit model obtained from a left-derived-functor instance. -/
@[stacks 05SA "canonical derived colimit model"]
noncomputable def derivedColimitModel
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (C ⥤ A)] [HasColimitsOfShape C A]
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived C A)
      (HomotopyCategory.quasiIso (C ⥤ A) (up ℤ))] :
    ColimitModel C A where
  functor := derivedColimit C A
  counit :=
    (colimitToDerived C A).totalLeftDerivedCounit
      (DerivedCategory.Qh :
        HomotopyCategory (C ⥤ A) (up ℤ) ⥤ DerivedCategory (C ⥤ A))
      (HomotopyCategory.quasiIso (C ⥤ A) (up ℤ))
  isLeftDerived := sorry

/-- Any explicit colimit model is canonically identified with the total left-derived colimit.
The comparison is obtained from the universal property, so downstream code can transport along a
model without rebuilding a local derived-functor instance. -/
@[stacks 05SA "explicit colimit model comparison"]
noncomputable def ColimitModel.isoDerivedColimit
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (C ⥤ A)] [HasColimitsOfShape C A]
    (M : ColimitModel C A)
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived C A)
      (HomotopyCategory.quasiIso (C ⥤ A) (up ℤ))] :
    M.functor ≅ derivedColimit C A :=
  LeftDerived.Model.iso M (derivedColimitModel C A)

end CategoryTheory.Functor
