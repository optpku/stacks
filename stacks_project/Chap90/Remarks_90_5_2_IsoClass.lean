/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass

/-!
# Fiberwise isomorphism-class functors of cofibered categories

The chosen-cleavage fibre action and fibrewise isomorphism-class functor are owned by
`ReasLib.CategoryTheory.Cofibered.FiberIsoClass`.
-/

@[expose] public section

namespace CategoryTheory

universe u v w vS
open scoped Bicategory
variable {C : Type u} [Category.{v} C] {F : Type w} [Category.{vS} F]
variable (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]

#check (CategoryTheory.Functor.fiberIsoClassFunctor p : C ⥤ Type w)
variable {X Y : CofiberedCategoryOver.Groupoids.{u, v, w, vS} C} (φ : X ⟶ Y)
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.fiberIsoClassFunctorMap φ :
  Functor.fiberIsoClassFunctor X.p ⟶ Functor.fiberIsoClassFunctor Y.p)

end CategoryTheory
