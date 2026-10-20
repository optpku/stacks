/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Connected.BaseChange
import StacksCheckRecall

/-!
# Geometric connectedness after field extension

Geometric connectedness of an algebraic space over a field is invariant under
extension of the ground field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected

/- Lemma 72.12.2: Let `X` be an algebraic space over the field `k`. Let `k'/k` be
a field extension. Then `X` is geometrically connected over `k` if and only if
the base change of `X` along `FieldExtension.specMap k k'` is geometrically
connected over `k'`. -/
@[stacks 0A10] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected.iff_fieldExtension :
    ∀ {k : Type u} [Field k] {k' : Type u} [Field k']
      [Algebra k k'] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyConnected X ↔
      GeometricallyConnected (baseChange (FieldExtension.specMap k k') X))

#check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected.instGeometricallyConnected_baseChange :
    ∀ {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
      (X : AlgebraicSpace (Spec (of k))) [GeometricallyConnected X],
    GeometricallyConnected (baseChange (FieldExtension.specMap k k') X))

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
