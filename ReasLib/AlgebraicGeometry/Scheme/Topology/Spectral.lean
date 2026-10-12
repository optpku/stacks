/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Spectral.Basic

@[expose] public section

/-!
# Spectral topologies on schemes

Quasi-compact, quasi-separated schemes carry the canonical structure of spectral spaces.
-/

universe u

namespace AlgebraicGeometry.Scheme

/-- The underlying topological space of a quasi-compact and quasi-separated scheme is spectral. -/
instance instSpectralSpace (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    SpectralSpace X :=
  SpectralSpace.mk

end AlgebraicGeometry.Scheme
