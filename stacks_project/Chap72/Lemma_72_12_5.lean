module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Connected.SeparableClosure

/-!
# Geometric connectedness after base change to a separable algebraic closure

An algebraic space over a field `k` is geometrically connected if and only if its
base change to a separable algebraic closure of `k` is connected.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected

/- Lemma 72.12.5: Let `k` be a field. Let `X` be an algebraic space over `k`.
Let `ksep` be a separable algebraic closure of `k`. Then `X` is geometrically
connected if and only if the base change of `X` along `FieldExtension.specMap k ksep`
is connected. -/
@[stacks 0A13] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected.iff_connectedSpace_baseChange_toSepClosure :
    ∀ {k : Type u} [Field k] {ksep : Type u} [Field ksep] [Algebra k ksep]
      [IsSepClosure k ksep] (X : AlgebraicSpace (Spec (of k))),
      GeometricallyConnected X ↔
        ConnectedSpace (Points (baseChange (FieldExtension.specMap k ksep) X)))

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
