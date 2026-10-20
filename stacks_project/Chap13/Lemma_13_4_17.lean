module

import Mathlib.CategoryTheory.Triangulated.Functor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.17

For a shift-compatible functor, preservation of distinguished triangles is
Mathlib's `Functor.IsTriangulated` property.  Its additive structure is the
canonical instance supplied by that owner.
-/

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [Limits.HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

@[stacks 05QY] #check (inferInstance : F.Additive)

end CategoryTheory
