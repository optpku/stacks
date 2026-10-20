module

public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Connected

/-!
# Connected components after extension of a separably closed field

If `k` is separably algebraically closed, then for any field extension `k'/k` the
morphism `X_{k'} ⟶ X` induces a bijection on connected components of points.
In particular, an algebraic space over `k` is geometrically connected if and only
if it is connected.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected

/-- For any field extension of a separably algebraically closed field, the canonical
projection from the base change of an algebraic space induces a bijection on connected
components of its space of points. -/
theorem connectedComponentsMap_bijective_of_isSepClosed {k k' : Type u} [Field k]
    [IsSepClosed k] [Field k'] [Algebra k k'] (X : AlgebraicSpace (Spec (of k))) :
    Function.Bijective
      ((Points.continuous_map (productSnd (ofOver (Over.mk (FieldExtension.specMap k k'))) X)).connectedComponentsMap :
        ConnectedComponents (Points (product (ofOver (Over.mk (FieldExtension.specMap k k'))) X)) →
          ConnectedComponents (Points X)) :=
  sorry

/-- An algebraic space over a separably algebraically closed field is geometrically
connected if and only if its space of points is connected. -/
theorem iff_connectedSpace_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyConnected X ↔ ConnectedSpace (Points X) :=
  sorry

/-- Over a separably algebraically closed field, a connected algebraic space is
geometrically connected. -/
instance instGeometricallyConnected_of_connectedSpace_of_isSepClosed {k : Type u}
    [Field k] [IsSepClosed k] (X : AlgebraicSpace (Spec (of k)))
    [ConnectedSpace (Points X)] : GeometricallyConnected X :=
  (iff_connectedSpace_of_isSepClosed X).mpr inferInstance

/-- Over a separably algebraically closed field, a geometrically connected algebraic
space has connected space of points. -/
instance instConnectedSpace_of_geometricallyConnected_of_isSepClosed {k : Type u}
    [Field k] [IsSepClosed k] (X : AlgebraicSpace (Spec (of k)))
    [GeometricallyConnected X] : ConnectedSpace (Points X) :=
  (iff_connectedSpace_of_isSepClosed X).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
