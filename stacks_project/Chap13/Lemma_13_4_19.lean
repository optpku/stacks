/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Triangulated.Functor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.19

Exactness is represented by the canonical `Functor.CommShift` and
`Functor.IsTriangulated` instances.  Both compose without a chapter-specific
construction.
-/

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section CommShift

variable {D : Type u₁} {D' : Type u₂} {D'' : Type u₃}
  [Category.{v₁} D] [Category.{v₂} D'] [Category.{v₃} D'']
  [HasShift D ℤ] [HasShift D' ℤ] [HasShift D'' ℤ]
  (F : D ⥤ D') (F' : D' ⥤ D'') [F.CommShift ℤ] [F'.CommShift ℤ]

@[stacks 014Y] #check (inferInstance : (F ⋙ F').CommShift ℤ)

end CommShift

section IsTriangulated

variable {D : Type u₁} {D' : Type u₂} {D'' : Type u₃}
  [Category.{v₁} D] [Category.{v₂} D'] [Category.{v₃} D'']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D'] [Limits.HasZeroObject D'']
  [HasShift D ℤ] [HasShift D' ℤ] [HasShift D'' ℤ]
  [Preadditive D] [Preadditive D'] [Preadditive D'']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [∀ n : ℤ, (shiftFunctor D'' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [Pretriangulated D'']
  (F : D ⥤ D') (F' : D' ⥤ D'')
  [F.CommShift ℤ] [F'.CommShift ℤ] [F.IsTriangulated] [F'.IsTriangulated]

@[stacks 014Y] #check (inferInstance : (F ⋙ F').IsTriangulated)

end IsTriangulated

end CategoryTheory
