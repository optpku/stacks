/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving.Base
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base

/-!
# Algebraic stacks locally of finite presentation are limit preserving

An algebraic stack over a scheme whose structure morphism is locally of finite
presentation is limit preserving, as is its structure morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- An algebraic stack over a scheme whose structure morphism is locally of
finite presentation is limit preserving. -/
@[stacks 0CMX]
instance toLimitPreserving {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation (baseProjection.{u + 1, u, u + 1} X)] :
    Groupoids.LimitPreserving X := sorry

/-- The structure morphism of an algebraic stack locally of finite presentation
over `S` is limit preserving as a 1-morphism of categories fibred in groupoids. -/
instance toHomLimitPreserving {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation (baseProjection.{u + 1, u, u + 1} X)] :
    Groupoids.Hom.LimitPreserving
      (baseProjection.{u + 1, u, u + 1} X) :=
  (Groupoids.LimitPreserving.iff_baseProjection X).mp inferInstance

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
