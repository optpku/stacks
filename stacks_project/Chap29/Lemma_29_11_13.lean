/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.11.13: A morphism between affine schemes is affine. -/
@[stacks 01SH] #check
  (AlgebraicGeometry.isAffineHom_of_isAffine :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
      AlgebraicGeometry.IsAffineHom f)
