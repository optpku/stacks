/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity

open CategoryTheory AlgebraicGeometry

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The geometric point obtained by postcomposing its scheme morphism. -/
abbrev GeometricPoint.imageHom {X S : Scheme.{u}} (xbar : GeometricPoint X) (f : X ⟶ S) :
    GeometricPoint S := xbar.map f

end AlgebraicGeometry.Scheme
