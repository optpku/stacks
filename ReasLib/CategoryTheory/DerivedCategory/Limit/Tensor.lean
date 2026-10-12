/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Functor.Additive.Constant
public import ReasLib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Tensor Products and Sequential Derived Limits

This leaf owns the two variable-fixed composites formed from the derived
constant-diagram functor, fixed-factor derived tensoring, and the total right
derived sequential inverse limit. The construction is independent of any
particular coefficient category.
@stack 091J
@stack 091K
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit

section

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
variable [MonoidalCategory A]
variable [h_monoidalPreadditive : MonoidalPreadditive (SequentialInverseSystem A)]
variable [∀ (K L : CochainComplex (SequentialInverseSystem A) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (SequentialInverseSystem A)) (up ℤ)]
variable [HasLimitsOfShape ℕᵒᵖ A]
variable [h_lim_additive : (lim : SequentialInverseSystem A ⥤ A).Additive]
variable [h_derivedFunctor : HasDerivedFunctor A]

/-- The derived constant-diagram functor followed by fixed-right derived tensoring with `E`. -/
@[stacks 08U1 "fixed-right tensor before derived limit"]
noncomputable abbrev tensorRightFactor
    (E : DerivedCategory (SequentialInverseSystem A))
    [h_tensor : DerivedCategory.DerivedTensor.Right.Has (C := SequentialInverseSystem A)] :
    DerivedCategory A ⥤ DerivedCategory (SequentialInverseSystem A) :=
  (((Functor.const ℕᵒᵖ : A ⥤ SequentialInverseSystem A).mapDerivedCategory :
    DerivedCategory A ⥤ DerivedCategory (SequentialInverseSystem A)) ⋙
      DerivedCategory.DerivedTensor.Right.functor E)

/-- Tensor a derived object of `A` with a fixed derived sequential inverse system, then take the
total right derived inverse limit. -/
@[stacks 08U1, stacks 091J "fixed-right tensor derived limit"]
noncomputable abbrev tensorRight
    (E : DerivedCategory (SequentialInverseSystem A))
    [h_tensor : DerivedCategory.DerivedTensor.Right.Has (C := SequentialInverseSystem A)] :
    DerivedCategory A ⥤ DerivedCategory A :=
  tensorRightFactor E ⋙ functor A

/-- Fixed-left derived tensoring after the derived constant-diagram functor on `K`. This is the
endofunctor of derived sequential inverse systems that precedes the derived inverse limit. -/
@[stacks 08U1 "fixed-left tensor before derived limit"]
noncomputable abbrev tensorLeftFactor
    (K : DerivedCategory A)
    [h_tensor : DerivedCategory.DerivedTensor.Left.Has (C := SequentialInverseSystem A)] :
    DerivedCategory (SequentialInverseSystem A) ⥤
      DerivedCategory (SequentialInverseSystem A) :=
  DerivedCategory.DerivedTensor.Left.functor
    (((Functor.const ℕᵒᵖ : A ⥤ SequentialInverseSystem A).mapDerivedCategory :
      DerivedCategory A ⥤ DerivedCategory (SequentialInverseSystem A)).obj K)

/-- Tensor a fixed derived object of `A` with a variable derived sequential inverse system, then
take the total right derived inverse limit. -/
@[stacks 08U1, stacks 091K "fixed-left tensor derived limit"]
noncomputable abbrev tensorLeft
    (K : DerivedCategory A)
    [h_tensor : DerivedCategory.DerivedTensor.Left.Has (C := SequentialInverseSystem A)] :
    DerivedCategory (SequentialInverseSystem A) ⥤ DerivedCategory A :=
  tensorLeftFactor K ⋙ functor A

end

end CategoryTheory.DerivedLimit
