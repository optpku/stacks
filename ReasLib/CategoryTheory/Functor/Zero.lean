/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero Functors

Functorial properties of the canonical zero functor, stated at the category-theoretic level rather
than for a particular module category.
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory.Limits
open scoped ZeroObject

universe v u

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

/-- Remark 12.29.4 (2) [03B9], generalized: the zero endofunctor of a category with a zero object
is a left adjoint. -/
@[stacks 03B9 "(2)"]
theorem zero_isLeftAdjoint :
    (0 : C ⥤ C).IsLeftAdjoint := sorry

/-- Remark 12.29.4 (2) [03B9], generalized: the zero endofunctor of a category with a zero object
preserves monomorphisms. -/
@[stacks 03B9 "(2)"]
theorem zero_preservesMonomorphisms :
    (0 : C ⥤ C).PreservesMonomorphisms := sorry

/-- Remark 12.29.4 (2) [03B9], generalized: a nonzero object prevents the zero endofunctor from
detecting zero objects. -/
@[stacks 03B9 "(2)"]
theorem zero_not_kernel_le_isZero_of_not_isZero {X : C} (hX : ¬ IsZero X) :
    ¬ ((0 : C ⥤ C).kernel ≤ IsZero) := sorry

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]

/-- Remark 12.29.4 (2) [03B9], generalized: in a category with a nonzero object, the zero
endofunctor is not faithful. -/
@[stacks 03B9 "(2)"]
theorem zero_not_faithful_of_not_isZero {X : C} (hX : ¬ IsZero X) :
    ¬ (0 : C ⥤ C).Faithful := sorry

end

end CategoryTheory.Functor
