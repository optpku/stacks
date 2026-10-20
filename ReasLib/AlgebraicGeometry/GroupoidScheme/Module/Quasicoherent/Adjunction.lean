/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Adjunctions for quasi-coherent modules on groupoid schemes

This module records conditions under which pullback of equivariant quasi-coherent modules along a
morphism of groupoid schemes is a left adjoint.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

variable {S : Scheme.{u}} {G H : GroupoidScheme S}

/-- If the target square is a pullback, equivariant pullback along a qcqs morphism into a flat
groupoid scheme is a left adjoint. -/
theorem pullbackOfTargetSquareIsLeftAdjoint (f : Hom G H)
    (hcart : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    [QuasiCompact f.obj.left] [QuasiSeparated f.obj.left]
    [Flat H.s.left] [Flat H.t.left] :
    (pullback f).IsLeftAdjoint := sorry

/-- Equivariant pullback along a cartesian qcqs morphism into a flat groupoid scheme is a left
adjoint. -/
theorem pullbackOfIsCartesianIsLeftAdjoint (f : Hom G H) (hf : f.IsCartesian)
    [QuasiCompact f.obj.left] [QuasiSeparated f.obj.left]
    [Flat H.s.left] [Flat H.t.left] :
    (pullback f).IsLeftAdjoint := by
  simpa using
    (pullbackOfTargetSquareIsLeftAdjoint f (Hom.targetSquare_isPullback f hf))

end AlgebraicGeometry.GroupoidScheme.QCoh
