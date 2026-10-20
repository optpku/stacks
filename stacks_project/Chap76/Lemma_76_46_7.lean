/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent.Noetherian
import StacksCheckRecall

/-!
# Pseudo-coherent morphisms over locally Noetherian algebraic spaces

A morphism of algebraic spaces into a locally Noetherian target is
pseudo-coherent if and only if it is locally of finite type.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 76.46.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `Y` is locally Noetherian, then `f` is
pseudo-coherent if and only if `f` is locally of finite type. -/
@[stacks 06BX] #check
  (AlgebraicGeometry.AlgebraicSpace.PseudoCoherent.iff_locallyOfFiniteType :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Y],
      AlgebraicGeometry.AlgebraicSpace.PseudoCoherent f ↔
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f)
