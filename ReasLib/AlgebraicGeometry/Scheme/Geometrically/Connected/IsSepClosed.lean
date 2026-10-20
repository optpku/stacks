module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.ConnectedComponents

/-!
# Geometric connectedness over separably closed fields

This module relates connectedness and geometric connectedness over separably closed fields and
describes connected components after arbitrary field extension.
-/

@[expose] public section

open CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Connected

/-- Over a separably closed field, the projection from an arbitrary field-extension base change
induces a bijection on connected components. -/
theorem connectedComponentsMap_bijective_of_isSepClosed
    {k K : Type u} [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Function.Bijective
      (((FieldExtension.toSource k K f).continuous.connectedComponentsMap) :
        ConnectedComponents (FieldExtension.baseChange k K f) → ConnectedComponents X) := sorry

end FieldExtension.Connected

namespace GeometricallyConnected

/-- Over a separably closed field, a scheme is geometrically connected exactly when its
underlying topological space is connected. -/
theorem iff_connectedSpace_of_isSepClosed
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    GeometricallyConnected f ↔ ConnectedSpace X := sorry

end GeometricallyConnected

end AlgebraicGeometry
