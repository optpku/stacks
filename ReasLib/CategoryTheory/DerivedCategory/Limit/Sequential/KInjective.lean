/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Replacement
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Resolution

/-!
# K-Injective Models for Sequential Derived Limits

This leaf specializes the generic stagewise-tower essential-surjectivity
criterion to the standard enough-injectives and exact-countable-products
hypotheses. The underlying K-injective replacement theorem remains owned by
the cochain-complex library.
@stack 08U5
@stack 0CQ9
@stack 0CQD
-/

@[expose] public section

open CategoryTheory.Limits

universe wA wSys v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

namespace DerivedLimit.Stage.TowerFunctor

/-- Lemma 15.87.11 (0CQ9), enough-injectives specialization: stagewise derived evaluation is
essentially surjective when the ambient category has enough injectives and exact countable
products. -/
@[stacks 0CQ9, stacks 0CQD, stacks 08U5]
theorem essSurj_of_enoughInjectives
    [EnoughInjectives A] [HasCountableProducts A] [CountableAB4Star A] :
    (DerivedLimit.Stage.towerFunctor A).EssSurj := sorry

end DerivedLimit.Stage.TowerFunctor

end

end CategoryTheory
