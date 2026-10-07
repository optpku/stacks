module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected

/-!
# Separable-Closure Test for Geometric Connectedness

This leaf owns the test of geometric connectedness after one chosen separable
closure. The closure is an explicit parameter, so the criterion applies to
any construction carrying the canonical `IsSepClosure` structure.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.GeometricallyConnected

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable {ksep : Type u} [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]

/-- A scheme over a field is geometrically connected exactly when its base change to a chosen
separable closure is connected. -/
theorem iff_connectedSpace_baseChange_toSepClosure :
    GeometricallyConnected f ↔
      ConnectedSpace (pullback f (Spec.map (ofHom (algebraMap k ksep))) : Scheme) := sorry

end AlgebraicGeometry.GeometricallyConnected
