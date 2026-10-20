/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-! # Yoneda compatibility of completed-stalk restrictions -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- The Yoneda morphism of a completed-stalk restriction is isomorphic to the
composite of the canonical completed-stalk map and the original Yoneda morphism. -/
theorem yonedaOfObject_completeLocalObject {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    Nonempty
      (yonedaOfObject (completeLocalObject hU x hx u0).base.toS
          (completeLocalObject hU x hx u0).object
          (completeLocalObject hU x hx u0).over_obj ≅
        overMap (fromSpecCompletionOverHom hU u0) ≫ yonedaOfObject hU x hx) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
