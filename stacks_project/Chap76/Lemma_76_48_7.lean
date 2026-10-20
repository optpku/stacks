/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/-
Lemma 76.48.7: Let `S` be a scheme. A Koszul-regular immersion of algebraic
spaces over `S` is a local complete intersection morphism.
-/
@[stacks 0CHK] #check
  (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion.isLocalCompleteIntersection :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S} (i : X ⟶ Y),
      [AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion i] →
        AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection i)
