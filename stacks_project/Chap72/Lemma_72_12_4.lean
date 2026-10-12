/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap72.Lemma_72_12_3

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

/-- Lemma 72.12.4 (1): Let `k'/k` be an extension of fields and let `X` be an algebraic
space over `k`. If `k` is separably algebraically closed, then the morphism
`productSnd (ofOver (Over.mk (FieldExtension.specMap k k'))) X` induces a bijection
on connected components of `Points` of the product and of `Points X`. -/
@[stacks 0A12]
theorem connectedComponentsMap_bijective_of_isSepClosed {k k' : Type u} [Field k]
    [IsSepClosed k] [Field k'] [Algebra k k'] (X : AlgebraicSpace (Spec (of k))) :
    Function.Bijective
      ((Points.continuous_map (productSnd (ofOver (Over.mk (FieldExtension.specMap k k'))) X)).connectedComponentsMap :
        ConnectedComponents (Points (product (ofOver (Over.mk (FieldExtension.specMap k k'))) X)) →
          ConnectedComponents (Points X)) :=
  sorry

/-- Lemma 72.12.4 (2): Let `X` be an algebraic space over a separably algebraically
closed field `k`. Then `X` is geometrically connected over `k` if and only if
`Points X` is connected. -/
@[stacks 0A12]
theorem iff_connectedSpace_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyConnected X ↔ ConnectedSpace (Points X) :=
  sorry

/-- Over a separably algebraically closed field, a connected algebraic space is
geometrically connected. -/
instance instGeometricallyConnected_of_connectedSpace_of_isSepClosed {k : Type u}
    [Field k] [IsSepClosed k] (X : AlgebraicSpace (Spec (of k)))
    [ConnectedSpace (Points X)] : GeometricallyConnected X :=
  sorry

/-- Over a separably algebraically closed field, a geometrically connected algebraic
space has connected space of points. -/
instance instConnectedSpace_of_geometricallyConnected_of_isSepClosed {k : Type u}
    [Field k] [IsSepClosed k] (X : AlgebraicSpace (Spec (of k)))
    [GeometricallyConnected X] : ConnectedSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
