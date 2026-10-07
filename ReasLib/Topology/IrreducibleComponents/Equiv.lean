module

public import Mathlib.Topology.Irreducible

/-!
# Irreducible components under homeomorphisms

This leaf packages the component correspondence induced by a homeomorphism.
It is deliberately topological, so scheme and Galois applications do not
need to rebuild the open-map-with-preirreducible-fibres construction.
-/

@[expose] public section

open Set

universe u v

namespace Homeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A fiber of a homeomorphism over a point is preirreducible. -/
theorem isPreirreducible_preimage_singleton (e : X ≃ₜ Y) (y : Y) :
    IsPreirreducible (e ⁻¹' ({y} : Set Y)) := sorry

/-- The equivalence between irreducible components induced by a homeomorphism. -/
noncomputable def irreducibleComponentsEquiv (e : X ≃ₜ Y) :
    irreducibleComponents X ≃ irreducibleComponents Y :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber e e.continuous e.isOpenMap
    (fun y ↦ e.isPreirreducible_preimage_singleton y) e.surjective).symm.toEquiv

/-- The component equivalence of a homeomorphism sends a component to its image. -/
theorem coe_irreducibleComponentsEquiv_apply
    (e : X ≃ₜ Y) (Z : irreducibleComponents X) :
    ((e.irreducibleComponentsEquiv Z : irreducibleComponents Y) : Set Y) = e '' (Z : Set X) := sorry

/-- The inverse component equivalence of a homeomorphism sends a component to its preimage. -/
theorem coe_irreducibleComponentsEquiv_symm_apply
    (e : X ≃ₜ Y) (Z : irreducibleComponents Y) :
    (((e.irreducibleComponentsEquiv).symm Z : irreducibleComponents X) : Set X) =
      e ⁻¹' (Z : Set Y) := sorry

end Homeomorph
