/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Opposite Views of Homological Functors

This module relates a homological functor on an opposite pretriangulated
category to its opposite-valued covariant form.
-/

namespace CategoryTheory.Functor

open CategoryTheory.Limits

-- This scoped namespace supplies the canonical pretriangulated structure on an
-- opposite category, which is needed to interpret `H.IsHomological`.
open CategoryTheory.Pretriangulated.Opposite

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]

/-- The opposite-valued covariant form of a homological functor on `Dᵒᵖ` is
homological. -/
@[stacks 0147]
instance rightOp_isHomological (H : Dᵒᵖ ⥤ A) [H.IsHomological] :
    H.rightOp.IsHomological := sorry

end CategoryTheory.Functor
