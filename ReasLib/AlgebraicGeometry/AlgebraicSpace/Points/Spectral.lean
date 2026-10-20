/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Spectral.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Spectral spaces of algebraic-space points

The space of points of a quasi-compact, absolutely quasi-separated algebraic space is spectral.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The space of points of a quasi-compact, absolutely quasi-separated algebraic space
over any scheme is a spectral space. -/
@[stacks 0A4G]
instance instSpectralSpacePoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] : SpectralSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
