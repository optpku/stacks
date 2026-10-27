/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector

/-! # Restriction of the quasi-coherent coreflector counit to flat objects -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids Functor.Fiber

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The counit of the quasi-coherent coreflection, restricted to the small étale
site of the scheme underlying a fiber object. -/
def LQCohFbc.toQCoh_counit_restrictToSmallEtale
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) (F : LQCohFbc X) :=
  (restrictModulesToSmallEtale X (fiberInclusion.obj x)).map
    ((LQCohFbc.inclusion X).map ((QCoh.toLQCohFbcAdjunction X).counit.app F))

/-- The quasi-coherent coreflector counit becomes an isomorphism on the small
étale site of any flat scheme object of an algebraic stack. -/
instance LQCohFbc.toQCoh_counit_restrictToSmallEtale_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
    (F : LQCohFbc X) :
    IsIso (LQCohFbc.toQCoh_counit_restrictToSmallEtale x F) := sorry

end AlgebraicGeometry.GroupoidsOver
