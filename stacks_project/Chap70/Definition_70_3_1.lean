/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
import StacksCheckRecall

/-!
# Limit-preserving functors and transformations on schemes over a base
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v

/- Definition 70.3.1 (1): a functor `F : (Over S)ᵒᵖ ⥤ Type` is limit preserving,
or locally of finite presentation over `S`, when it sends every directed inverse
limit of affine schemes over `S` to a colimit of sets. -/
@[stacks 049J] #check
  (AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits :
    ∀ (S : Scheme.{u}), ((Over S)ᵒᵖ ⥤ Type v) → Prop)

/- Definition 70.3.1 (2): a transformation `a : F ⟶ G` of functors `(Over S)ᵒᵖ ⥤ Type`
is limit preserving, or locally of finite presentation, when for every scheme `T`
over `S` and every section `y : G.obj (op T)` the fiber functor over `y` is limit
preserving over `T`. -/
@[stacks 049J] #check
  (AlgebraicGeometry.Scheme.Over.IsLimitPreserving :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v}, (F ⟶ G) → Prop)
