/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening

/-!
# Thickenings of algebraic spaces and their small étale ringed topoi

A morphism of algebraic spaces is a thickening if and only if its associated morphism of
small étale ringed topoi is a thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme is a thickening if and only if the
associated morphism of small étale ringed topoi is a thickening. -/
theorem isThickening_iff_ringedToposHom {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') :
    IsThickening i ↔ RingedSite.ToposHom.IsThickening (ringedToposHom i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
