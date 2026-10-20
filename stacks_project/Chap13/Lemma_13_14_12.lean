/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.12

The reusable third-vertex closure is owned by
`ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Triangulated`.  This source entry records the
two textbook specializations without retaining a source-local comparison-triangle construction.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D] [IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities] [IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation]
  [F.CommShift ℤ] [F.IsTriangulated]

variable (T : Triangle D) (hT : T ∈ distTriang D)
  (h₁ : Functor.RightDerived.ComputesAt F S T.obj₁)
  (h₂ : Functor.RightDerived.ComputesAt F S T.obj₂)

/- Lemma 13.14.12 (1) (`05SZ`): computation of a pointwise right-derived functor is closed
under the third vertex of a distinguished triangle. -/
@[stacks 05SZ] #check
  (Functor.RightDerived.ComputesAt.obj₃_of_triangle
    T hT h₁ h₂ : Functor.RightDerived.ComputesAt F S T.obj₃)

variable (h₁' : Functor.LeftDerived.ComputesAt F S T.obj₁)
  (h₂' : Functor.LeftDerived.ComputesAt F S T.obj₂)

/- Lemma 13.14.12 (2) (`05SZ`): computation of a pointwise left-derived functor is closed
under the third vertex of a distinguished triangle. -/
@[stacks 05SZ] #check
  (Functor.LeftDerived.ComputesAt.obj₃_of_triangle
    T hT h₁' h₂' : Functor.LeftDerived.ComputesAt F S T.obj₃)

end

end CategoryTheory
