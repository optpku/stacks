module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.LocallyFinite

/-!
# Irreducible Components of Locally Noetherian Schemes

Local finiteness of irreducible components of closed subschemes in a locally Noetherian
ambient scheme.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]

/-- The images of the irreducible components of a closed subscheme of a locally Noetherian
scheme form a locally finite family in the ambient scheme. -/
theorem locallyFinite_irreducibleComponents_of_isClosedImmersion :
    LocallyFinite fun W : irreducibleComponents Z ↦ i.base '' (W : Set Z) := sorry

end AlgebraicGeometry
