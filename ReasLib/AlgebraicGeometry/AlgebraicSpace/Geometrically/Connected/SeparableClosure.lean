module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically

/-!
# Geometric connectedness after base change to a separable algebraic closure

An algebraic space over a field `k` is geometrically connected if and only if its
base change to a separable algebraic closure of `k` is connected.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected

/-- An algebraic space over a field is geometrically connected if and only if its
base change to a chosen separable algebraic closure has connected space of points. -/
theorem iff_connectedSpace_baseChange_toSepClosure {k : Type u} [Field k]
    {ksep : Type u} [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyConnected X ↔
      ConnectedSpace (Points (baseChange (FieldExtension.specMap k ksep) X)) :=
  sorry

/-- If the base change of an algebraic space to its canonical separable closure is
connected, then the algebraic space is geometrically connected. -/
instance instGeometricallyConnected_of_connectedSpace_baseChange_toSepClosure
    {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k)))
    [ConnectedSpace (Points (baseChange (FieldExtension.specMap k (SeparableClosure k)) X))] :
    GeometricallyConnected X :=
  (iff_connectedSpace_baseChange_toSepClosure (ksep := SeparableClosure k) X).mpr inferInstance

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
