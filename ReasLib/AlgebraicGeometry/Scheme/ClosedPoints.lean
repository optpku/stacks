/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every nonempty quasi-compact scheme has a closed point. -/
theorem exists_closedPoint_of_compactSpace (X : Scheme.{u}) [CompactSpace X] [Nonempty X] :
    (closedPoints X).Nonempty := sorry

end AlgebraicGeometry.Scheme
