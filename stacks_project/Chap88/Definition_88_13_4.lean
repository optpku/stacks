/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Flat
public import stacks_project.Chap88.Definition_88_20_1_Comparison
public import stacks_project.Chap88.Definition_88_20_1_Etale

/-!
# Flat morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 88.13.4: A morphism of locally Noetherian formal algebraic spaces
is flat when every affine formal étale chart square has its upper arrow induced
by a flat map of adic Noetherian topological rings. -/
@[stacks 0GCC] #check (AlgebraicGeometry.FormalAlgebraicSpace.Flat :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsLocallyNoetherian X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsLocallyNoetherian Y],
    (X ⟶ Y) → Prop)
