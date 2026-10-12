/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Idempotents.Countable
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Idempotent Completeness of Pretriangulated Categories

In a pretriangulated category, split morphisms have the expected kernels and
cokernels. Combined with the generic countable criteria in
`CategoryTheory.Idempotents.Countable`, this yields idempotent completeness
from countable products or countable coproducts.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Limits

/-- A split epimorphism in a pretriangulated category has a kernel. -/
instance (priority := 100) hasKernel_of_splitEpi
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    HasKernel f := sorry

/-- A split monomorphism in a pretriangulated category has a cokernel. -/
instance (priority := 100) hasCokernel_of_splitMono
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    HasCokernel f := sorry

/-- A pretriangulated category with countable products is idempotent complete. -/
@[stacks 05QW]
instance (priority := 100) isIdempotentComplete_of_countableProducts
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasCountableProducts C] :
    IsIdempotentComplete C := sorry

/-- A pretriangulated category with countable coproducts is idempotent complete. -/
@[stacks 05QW]
instance (priority := 100) isIdempotentComplete_of_countableCoproducts
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasCountableCoproducts C] :
    IsIdempotentComplete C := sorry

end CategoryTheory.Pretriangulated
