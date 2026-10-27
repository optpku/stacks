/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor

/-! # Scheme thickenings as algebraic-space thickenings -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A first-order thickening of schemes over `S` remains a first-order thickening after
passing to algebraic spaces via `ofOverMap`. -/
instance instIsFirstOrderThickening_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (g : U ⟶ V) [AlgebraicGeometry.IsFirstOrderThickening g.left] :
    IsFirstOrderThickening ((ofOverFunctor S).map g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
