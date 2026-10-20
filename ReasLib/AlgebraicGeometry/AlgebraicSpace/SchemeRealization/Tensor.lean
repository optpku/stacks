/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-! # Realization and tensor products in the slice over the base scheme -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-- Comparison from the algebraic-space fibre product of `ofOver X` and `ofOver Y`
over `S` to `ofOver` of the scheme-level tensor product. -/
def sliceTensorComparison {S : Scheme.{u}} (X Y : Over S) :
    ((ofOverSlice S).obj X ⊗ (ofOverSlice S).obj Y).left ⟶ ofOver (X ⊗ Y) where
  app T := ↾fun p ↦
    (ofOverMap
      (lift (ofOverPoint ((fst ((ofOverSlice S).obj X) ((ofOverSlice S).obj Y)).left.app T p))
        (ofOverPoint ((snd ((ofOverSlice S).obj X) ((ofOverSlice S).obj Y)).left.app T p)))).app T
      (ofOverIdPoint T.unop)
  naturality := sorry

/-- The component of `sliceTensorComparison` at a test scheme is `ofOverMap` of the Cartesian
lift of the two projections. -/
theorem sliceTensorComparison_app {S : Scheme.{u}} (X Y : Over S) (T : (Over S)ᵒᵖ)
    (p : ((ofOverSlice S).obj X ⊗ (ofOverSlice S).obj Y).left.functorOfPoints.obj T) :
    (sliceTensorComparison X Y).app T p =
      (ofOverMap
        (lift (ofOverPoint ((fst ((ofOverSlice S).obj X) ((ofOverSlice S).obj Y)).left.app T p))
          (ofOverPoint ((snd ((ofOverSlice S).obj X) ((ofOverSlice S).obj Y)).left.app T p)))).app T
        (ofOverIdPoint T.unop) := sorry

end AlgebraicGeometry.AlgebraicSpace.SchemeRealization
