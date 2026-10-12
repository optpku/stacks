/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

/-!
# Generic Points of Scheme Components

This module provides the `X⁰` notation for the canonical set `genericPoints X`
of generic points of irreducible components.
-/

@[expose] public section

namespace AlgebraicGeometry

namespace _root_.AlgebraicGeometry

/-- Notation for the canonical generic points of irreducible components. -/
scoped[AlgebraicGeometry] notation:max X:max "⁰" => genericPoints X

end _root_.AlgebraicGeometry

end AlgebraicGeometry
