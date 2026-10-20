/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.IrreducibleComponents
import StacksCheckRecall

/-!
# Local finiteness of irreducible components

On a locally Noetherian algebraic space, the irreducible components of any
closed subset of the points space form a locally finite family.
-/

@[expose] public section

universe u

/- Lemma 72.6.1: Let `S` be a scheme and let `X` be a locally Noetherian
algebraic space over `S`. If `T` is a closed subset of `Points X`, then the
collection of irreducible components of `T` is locally finite. -/
@[stacks 0EE5] #check (AlgebraicGeometry.AlgebraicSpace.locallyFinite_irreducibleComponents :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
    {T : Set (AlgebraicGeometry.AlgebraicSpace.Points X)},
    IsClosed T → LocallyFinite (fun W : irreducibleComponents T ↦ Subtype.val '' (W : Set T)))
