/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Chow
import StacksCheckRecall

universe u

/- Lemma 69.18.1
A separated finite-type algebraic space over an affine scheme admits a proper
surjective morphism from an H-quasi-projective scheme over the same base.
-/
@[stacks 089J] #check
  (AlgebraicGeometry.AlgebraicSpace.WeakChowModification.exists_of_separated_finiteType :
    ∀ {A : Type u} [CommRing A]
      (X : AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec (CommRingCat.of A)))
      [AlgebraicGeometry.AlgebraicSpace.Separated
        (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X)]
      [AlgebraicGeometry.AlgebraicSpace.FiniteType
        (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X)],
      Nonempty (AlgebraicGeometry.AlgebraicSpace.WeakChowModification X))
