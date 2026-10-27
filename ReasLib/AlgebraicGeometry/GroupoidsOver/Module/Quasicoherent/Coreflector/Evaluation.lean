/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.FlatRestriction

/-! # Evaluation of the quasi-coherent coreflection counit -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids Functor.Fiber Opposite

noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver.LQCohFbc

variable {S : Scheme.{u}}

/-- The canonical quasi-coherent coreflection counit evaluated at a fiber object. -/
def toQCohCounitEval {Y : GroupoidsOver S} [AlgebraicStack Y] {V : Over S}
    (y : Y.p.Fiber V) (G : LQCohFbc Y) :=
  ((inclusion Y).map ((QCoh.toLQCohFbcAdjunction Y).counit.app G)).val.app
    (op (fiberInclusion.obj y))

/-- Counit evaluation is the component of the included canonical counit. -/
theorem toQCohCounitEval_eq {Y : GroupoidsOver S} [AlgebraicStack Y]
    {V : Over S} (y : Y.p.Fiber V) (G : LQCohFbc Y) :
    toQCohCounitEval y G =
      ((inclusion Y).map ((QCoh.toLQCohFbcAdjunction Y).counit.app G)).val.app
        (op (fiberInclusion.obj y)) := rfl

/-- The quasi-coherent coreflection counit evaluates to an isomorphism at a flat object. -/
instance toQCohCounitEval_isIso {Y : GroupoidsOver S} [AlgebraicStack Y]
    {V : Over S} (y : Y.p.Fiber V)
    [AlgebraicStack.Flat (YonedaSlice.representative y)] (G : LQCohFbc Y) :
    IsIso (toQCohCounitEval y G) := sorry

end AlgebraicGeometry.GroupoidsOver.LQCohFbc
