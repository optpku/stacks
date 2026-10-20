module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.HomotopyLimit.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Single
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived limits of degree-zero inverse systems

This leaf specializes the standard Grothendieck derived-limit model to an ordinary sequential
inverse system embedded in degree zero.  The result uses the presentation-independent homotopy
limit predicate and the reusable stagewise tower isomorphism.
@stack 0CQD
@stack 0D2L
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wSys u v

namespace CategoryTheory.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- Lemma 15.103.3 (0D2L): the total right derived inverse limit of a degree-zero sequential
system is a homotopy limit of the tower obtained by embedding its individual stages in degree
zero. -/
@[stacks 0CQD, stacks 0D2L "derived limit of a degree-zero inverse system"]
theorem singleIsOf
    [IsGrothendieckAbelian.{w} A]
    [IsGrothendieckAbelian.{w} (SequentialInverseSystem A)]
    [HasLimitsOfShape ℕᵒᵖ A]
    [HasCountableProducts A] [CountableAB4Star A]
    [PreservesLimitsOfShape (Discrete ℕ) (lim : SequentialInverseSystem A ⥤ A)]
    (M : SequentialInverseSystem A) :
    HomotopyLimit.IsOf
      (M ⋙ DerivedCategory.singleFunctor A (0 : ℤ))
      ((functor A).obj
        ((DerivedCategory.singleFunctor (SequentialInverseSystem A) (0 : ℤ)).obj M)) := sorry

end CategoryTheory.DerivedLimit
