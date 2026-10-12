/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sequential Derived Limit in a Grothendieck Abelian Category

@stack 0CQD

This leaf derives the existence of the total right derived inverse-limit
functor from Grothendieck-abelian hypotheses.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w wA u v

namespace CategoryTheory.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasLimitsOfShape ℕᵒᵖ A]

namespace HasDerivedFunctor

/-- Grothendieck-abelian sequential inverse systems admit the canonical total
right derived inverse-limit functor. -/
@[stacks 0CQD]
instance ofGrothendieck
    [HasDerivedCategory.{wA} A]
    [(lim : SequentialInverseSystem A ⥤ A).Additive]
    [IsGrothendieckAbelian.{w} (SequentialInverseSystem A)] :
    HasDerivedFunctor A := sorry

end HasDerivedFunctor

end CategoryTheory.DerivedLimit
