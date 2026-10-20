/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranch

/-!
# Geometric unibranchness of group algebraic spaces over fields

A group algebraic space over a field is geometrically unibranch.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- A group algebraic space over the spectrum of a field is geometrically unibranch. -/
instance instIsGeometricallyUnibranch {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))) :
    AlgebraicSpace.IsGeometricallyUnibranch G.X.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
