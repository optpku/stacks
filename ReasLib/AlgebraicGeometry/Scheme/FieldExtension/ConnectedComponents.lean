module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.Topology.ConnectedComponents.Maps
public import ReasLib.Topology.ConnectedComponents.Set
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Connected components after field extension

This leaf records image and preimage theorems for connected components under the canonical source
projection of a field-extension base change. The object is presented with the standard
`FieldExtension.baseChange` orientation, so downstream arguments do not need to choose an order for
the raw pullback.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Connected

/-- The image of a connected component under the source projection of a field-extension base
change is the connected component of its image point. -/
theorem image_component_eq
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (x : FieldExtension.baseChange k K f) :
    (FieldExtension.toSource k K f).base '' connectedComponent x =
      connectedComponent ((FieldExtension.toSource k K f).base x) := sorry

/-- For a finite-dimensional field extension, the source projection of a base change sends each
connected component onto the connected component of its image point. -/
theorem image_component_eq_of_finiteDimensional
    {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (x : FieldExtension.baseChange k K f) :
    (FieldExtension.toSource k K f).base '' connectedComponent x =
      connectedComponent ((FieldExtension.toSource k K f).base x) := sorry

/-- The preimage of a connected component under the source projection of a field-extension base
change is saturated under connected components. -/
theorem preimage_component_isConnectedComponentSaturated
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (C : ConnectedComponents X) :
    Set.IsConnectedComponentSaturated
      ((FieldExtension.toSource k K f).base ⁻¹' C.set) := sorry

end FieldExtension.Connected

end AlgebraicGeometry
