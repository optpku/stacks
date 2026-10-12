/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Total Left Derived Functors from the Homotopy Category

@stack 05S9

This module gives the construction-neutral total left derived functor of an additive functor,
its homotopy- and cochain-level counits, and the corresponding universal-property statements.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA wA uB vB wB

namespace CategoryTheory.Functor.LeftDerived.Homotopy

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The total left derived functor of an additive functor, using its canonical functor from the
homotopy category to the target derived category. -/
@[stacks 05S9]
abbrev functor (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (Functor.Homotopy.toDerived F).totalLeftDerived
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))

/-- The canonical counit from the total left derived functor to the homotopy-to-derived functor. -/
@[stacks 05S9]
noncomputable abbrev counit (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ functor F ⟶
      Functor.Homotopy.toDerived F :=
  (Functor.Homotopy.toDerived F).totalLeftDerivedCounit
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))

/-- The cochain-level counit comparing the total left derived functor with termwise application. -/
@[stacks 05S9]
noncomputable def cochainCounit (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙ functor F ⟶
      F.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B) :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) (functor F)).inv ≫
    (Functor.associator
      (HomotopyCategory.quotient A (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
      (functor F)).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (up ℤ)) (counit F) ≫
    (Functor.Homotopy.cochainIso F).hom

/-- The homotopy-level counit exhibits `functor F` as a left derived functor. -/
@[stacks 05S9]
theorem isLeftDerived (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    (functor F).IsLeftDerivedFunctor (counit F)
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

/-- The cochain-level counit exhibits `functor F` as a left derived functor at quasi-isomorphisms. -/
@[stacks 05S9]
theorem cochainIsLeftDerived (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    (functor F).IsLeftDerivedFunctor (cochainCounit F)
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry

end CategoryTheory.Functor.LeftDerived.Homotopy
