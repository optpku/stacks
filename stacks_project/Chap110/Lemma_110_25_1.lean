/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.NonChevalley
import StacksCheckRecall

universe u

open CategoryTheory
open scoped AlgebraicGeometry

/- Lemma 110.25.1 -/
@[stacks 0GZM]
#check (AlgebraicGeometry.exists_affine_finitePresentation_locallyClosed_image_not_finiteUnion :
    ∃ (X Y : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsAffine X)
      (_ : AlgebraicGeometry.IsAffine Y) (f : X ⟶ Y)
      (_ : AlgebraicGeometry.Scheme.Hom.FinitePresentation f) (T : Set X),
      IsLocallyClosed T ∧ ¬ IsFiniteUnionOfLocallyClosed (f.base '' T))
