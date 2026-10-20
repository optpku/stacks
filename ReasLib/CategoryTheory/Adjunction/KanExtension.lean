/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Kan extensions from adjunctions

A left adjoint functor automatically has pointwise right Kan extensions,
and a right adjoint functor automatically has pointwise left Kan extensions.
These are global instances so that `sheafPushforwardCocontinuous` and related
constructions elaborate without manual `letI` plumbing.
-/

@[expose] public section

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A left adjoint `u` has pointwise right Kan extensions along `u.op`
(via initial objects in structured arrow categories). -/
instance instRightKanExtension_of_isLeftAdjoint
    (u : C ⥤ D) [u.IsLeftAdjoint] (P : Cᵒᵖ ⥤ Type w) :
    u.op.HasPointwiseRightKanExtension P := sorry

/-- A right adjoint `v` has pointwise left Kan extensions along `v.op`
(via terminal objects in costructured arrow categories). -/
instance instLeftKanExtension_of_isRightAdjoint
    (v : D ⥤ C) [v.IsRightAdjoint] (P : Dᵒᵖ ⥤ Type w) :
    v.op.HasPointwiseLeftKanExtension P := sorry

end Functor

end CategoryTheory
