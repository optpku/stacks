/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

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

/-- An algebraic space over a field is geometrically connected if and only if its
base change along a field extension is geometrically connected. -/
@[stacks 0A10]
theorem iff_fieldExtension {k : Type u} [Field k] {k' : Type u} [Field k']
    [Algebra k k'] (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyConnected X ↔
      GeometricallyConnected (baseChange (FieldExtension.specMap k k') X) :=
  sorry

/-- A geometrically connected algebraic space remains geometrically connected after
base change along a field extension. -/
instance instGeometricallyConnected_baseChange {k : Type u} [Field k] {k' : Type u}
    [Field k'] [Algebra k k'] (X : AlgebraicSpace (Spec (of k)))
    [GeometricallyConnected X] :
    GeometricallyConnected (baseChange (FieldExtension.specMap k k') X) :=
  (iff_fieldExtension X).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
