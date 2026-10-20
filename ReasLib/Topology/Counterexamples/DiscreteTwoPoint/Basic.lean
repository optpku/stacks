module

public import Mathlib.Topology.Category.TopCat.Basic

/-!
# The discrete two-point collapse

This module owns the concrete map from a discrete two-point space to a point.
It is independent of sheaves and can be reused by topological and categorical
counterexamples built from the same map.
-/

@[expose] public section

open CategoryTheory

namespace TopCat.Counterexample.DiscreteTwoPoint

/-- The discrete topological space on two points. -/
abbrev space : TopCat := TopCat.discrete.obj (Fin 2)

/-- The one-point discrete topological space. -/
abbrev point : TopCat := TopCat.discrete.obj PUnit

/-- The continuous map collapsing both points of `space` to the unique point
of `point`. -/
def collapse : space ⟶ point :=
  TopCat.discrete.map (TypeCat.ofHom (fun _ : Fin 2 ↦ PUnit.unit))

end TopCat.Counterexample.DiscreteTwoPoint
