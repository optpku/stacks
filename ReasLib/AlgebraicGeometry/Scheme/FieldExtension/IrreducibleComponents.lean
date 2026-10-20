/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleComponents

/-!
# Irreducible components after field extension

This module gives the component map induced by the projection from a field
extension base change of an arbitrary scheme morphism to `Spec k`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Irreducible

/-- The image of an irreducible component under the projection from a field-extension base change
is an irreducible component of the original scheme. -/
@[stacks 04KX]
theorem image_component
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents (FieldExtension.baseChange k K f)) :
    (FieldExtension.toSource k K f).base '' (T : Set (FieldExtension.baseChange k K f)) ∈
      irreducibleComponents X := sorry

/-- The canonical map on irreducible components induced by the source projection of a field
extension base change. -/
@[stacks 04KX]
noncomputable def componentsMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    irreducibleComponents (FieldExtension.baseChange k K f) → irreducibleComponents X :=
  fun T ↦
    ⟨(FieldExtension.toSource k K f).base '' (T : Set (FieldExtension.baseChange k K f)),
      image_component k K f T⟩

/-- The underlying set of the field-extension component map is the image under the source
projection. -/
theorem coe_componentsMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents (FieldExtension.baseChange k K f)) :
    ((componentsMap k K f T : irreducibleComponents X) : Set X) =
      (FieldExtension.toSource k K f).base '' (T : Set (FieldExtension.baseChange k K f)) :=
  sorry

/-- The component map induced by a field-extension base change is surjective. -/
@[stacks 04KX]
theorem componentsMap_surjective
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Function.Surjective (componentsMap k K f) := sorry

/-- The canonical fibre of the irreducible-component map over a component of `X`. -/
@[stacks 04KW]
def fiber
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents X) :
    Set (irreducibleComponents (FieldExtension.baseChange k K f)) :=
  {Z | componentsMap k K f Z = T}

/-- Membership in the canonical component fibre is exactly equality under `componentsMap`. -/
theorem mem_fiber_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents X)
    (Z : irreducibleComponents (FieldExtension.baseChange k K f)) :
    Z ∈ fiber k K f T ↔ componentsMap k K f Z = T := Iff.rfl

/-- The inverse image of a component is the union of the components in its canonical fibre. -/
@[stacks 04KW]
theorem preimage_component_eq_iUnion_fiber
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents X) :
    (FieldExtension.toSource k K f) ⁻¹' (T : Set X) =
      ⋃ Z ∈ fiber k K f T, (Z : Set (FieldExtension.baseChange k K f)) := sorry

/-- The inverse image of an irreducible component under a field-extension projection is a union
of irreducible components of the base change. -/
@[stacks 04KW]
theorem preimage_component_eq_iUnion
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents X) :
    ∃ A : Set (irreducibleComponents (FieldExtension.baseChange k K f)),
      (FieldExtension.toSource k K f) ⁻¹' (T : Set X) =
        ⋃ Z ∈ A, (Z : Set (FieldExtension.baseChange k K f)) := sorry

/-- If the extension-base spectrum is geometrically irreducible, the source projection of its
field-extension base change induces an equivalence on irreducible components. -/
noncomputable def componentsEquiv_of_geometricallyIrreducible
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (h : GeometricallyIrreducible (FieldExtension.specMap k K)) :
    irreducibleComponents (FieldExtension.baseChange k K f) ≃ irreducibleComponents X :=
  _root_.AlgebraicGeometry.GeometricallyIrreducible.pullbackFstComponentsEquiv_of f
    (FieldExtension.specMap k K) h

/-- Over a separably closed field, the source projection of a field-extension base change induces
an equivalence on irreducible components. -/
@[stacks 038H]
noncomputable abbrev componentsEquiv_of_isSepClosed
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    irreducibleComponents (FieldExtension.baseChange k K f) ≃ irreducibleComponents X :=
  componentsEquiv_of_geometricallyIrreducible k K f
    FieldExtension.GeometricallyIrreducible.of_isSepClosed

/-- The separably closed field-extension component equivalence sends a component to its image
under the source projection. -/
theorem coe_componentsEquiv_apply
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : irreducibleComponents (FieldExtension.baseChange k K f)) :
    ((componentsEquiv_of_isSepClosed k K f T :
        irreducibleComponents X) : Set X) =
      (FieldExtension.toSource k K f).base ''
        (T : Set (FieldExtension.baseChange k K f)) := sorry

end FieldExtension.Irreducible

end AlgebraicGeometry
