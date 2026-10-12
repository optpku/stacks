/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor

@[expose] public section

/-!
# Comparison Units for Sequential Derived Limit

This leaf exposes the homotopy- and cochain-level units and their right-derived
universal properties.
@stack 0CQD
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
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
variable [(lim : SequentialInverseSystem A ⥤ A).Additive]
variable [HasDerivedFunctor A]

/-- The canonical homotopy-level unit comparing inverse limit with its total
right derived functor. -/
@[stacks 0CQD]
noncomputable abbrev unit :
    Functor.Homotopy.toDerived (lim : SequentialInverseSystem A ⥤ A) ⟶
      (DerivedCategory.Qh :
        HomotopyCategory (SequentialInverseSystem A) (up ℤ) ⥤
          DerivedCategory (SequentialInverseSystem A)) ⋙ functor A :=
  Functor.RightDerived.Homotopy.unit
    (lim : SequentialInverseSystem A ⥤ A)

/-- The canonical cochain-level unit comparing termwise inverse limit with its
total right derived functor. -/
@[stacks 0CQD]
noncomputable abbrev cochainUnit :
    (lim : SequentialInverseSystem A ⥤ A).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⟶
      (DerivedCategory.Q :
        CochainComplex (SequentialInverseSystem A) ℤ ⥤
          DerivedCategory (SequentialInverseSystem A)) ⋙ functor A :=
  Functor.RightDerived.Homotopy.cochainUnit
    (lim : SequentialInverseSystem A ⥤ A)

/-- The homotopy-level unit exhibits `functor A` as the total right derived
functor of sequential inverse limit. -/
@[stacks 0CQD]
theorem isRightDerived :
    (functor A).IsRightDerivedFunctor (unit A)
      (HomotopyCategory.quasiIso (SequentialInverseSystem A) (up ℤ)) := sorry

/-- The cochain-level unit exhibits `functor A` as a right derived functor at
quasi-isomorphisms. -/
@[stacks 0CQD]
theorem cochainIsRightDerived :
    (functor A).IsRightDerivedFunctor (cochainUnit A)
      (HomologicalComplex.quasiIso (SequentialInverseSystem A) (up ℤ)) := sorry

end CategoryTheory.DerivedLimit
