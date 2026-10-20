/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypeOver
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Versal

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The spectrum morphism of a complete local object with formally versal
maximal-adic restriction is flat when the algebraic stack is locally of finite
type over a locally Noetherian scheme. -/
instance isFlat_yonedaOfObject {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x : CompleteLocalObject X)
    [hversal : GroupoidsOver.FormalObject.IsVersal (FormalObject.restriction x)] :
    Flat (yonedaOfObject x.base.toS x.object x.over_obj) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
