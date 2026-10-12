/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.Topology.Noetherian.Basic

@[expose] public section

universe u

namespace AlgebraicGeometry.IsLocallyNoetherian

/-- The underlying topological space of a locally Noetherian scheme is locally Noetherian. -/
instance (priority := 100) locallyNoetherianSpace {X : Scheme.{u}} [IsLocallyNoetherian X] :
    TopologicalSpace.LocallyNoetherianSpace X := sorry

end AlgebraicGeometry.IsLocallyNoetherian
