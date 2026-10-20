module

public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.Topology.ConnectedComponents.Finite

/-!
# Finite connected components after field extension

This leaf specializes the compact/open component criterion to field-extension base changes and
records the finite-type openness consequence used by geometric applications.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Connected

/-- A compact source with open connected components after field extension has finitely many
connected components after that extension. -/
theorem finite_components_of_compact_open
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]
    (hopen : ∀ x : FieldExtension.baseChange k K f, IsOpen (connectedComponent x)) :
    Finite (ConnectedComponents (FieldExtension.baseChange k K f)) := sorry

/-- For a finite-type scheme over a field, connected components remain open after a field
extension. -/
theorem isOpen_component_of_finiteType
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Scheme.Hom.FiniteType f]
    (x : FieldExtension.baseChange k K f) :
    IsOpen (connectedComponent x) := sorry

end FieldExtension.Connected

end AlgebraicGeometry
