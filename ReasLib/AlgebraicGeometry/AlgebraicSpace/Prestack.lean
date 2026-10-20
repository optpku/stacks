/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- The projection from algebraic spaces over schemes over `S` to the fppf site of
schemes over `S` is fibered and has sheaf Hom presheaves. -/
@[stacks 04UA]
instance instIsPrestackOnSite (S : Scheme.{u}) :
    IsPrestack.OnSite (Scheme.fppfTopology.over S)
      (Comma.snd (𝟭 (AlgebraicSpace S)) (ofOverFunctor S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
