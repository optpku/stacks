/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational.Dominant
import StacksCheckRecall

/-!
# Birational morphisms of decent algebraic spaces are dominant

A birational morphism of decent algebraic spaces with finitely many irreducible
components is dominant.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.22.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which are decent and have finitely many irreducible components.
If `f` is birational then `f` is dominant. -/
@[stacks 0ACW] #check
  (AlgebraicGeometry.AlgebraicSpace.Dominant.of_isBirational :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f], Dominant f)
