/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Preadditive.Limits

@[expose] public section

/-!
# The Total Derived Functor of Sequential Inverse Limit

@stack 0CQD

This module owns only the derivability input and the canonical total right
derived inverse-limit functor.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasLimitsOfShape ℕᵒᵖ A]

/-- The derivability input needed to form the total right derived sequential
inverse-limit functor. This is a transparent specialization of Mathlib's
`Functor.HasRightDerivedFunctor`. -/
@[stacks 0CQD]
abbrev HasDerivedFunctor [(lim : SequentialInverseSystem A ⥤ A).Additive] : Prop :=
    (Functor.Homotopy.toDerived (lim : SequentialInverseSystem A ⥤ A)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SequentialInverseSystem A) (up ℤ))

variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- The canonical total right derived inverse-limit functor on sequential
inverse systems. -/
@[stacks 0CQD]
noncomputable abbrev functor
    [(lim : SequentialInverseSystem A ⥤ A).Additive]
    [HasDerivedFunctor A] :
    DerivedCategory (SequentialInverseSystem A) ⥤ DerivedCategory A :=
  Functor.RightDerived.Homotopy.functor
    (lim : SequentialInverseSystem A ⥤ A)

end CategoryTheory.DerivedLimit
