/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.LocalCompleteIntersection

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 76.48.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is syntomic if and only if `f` is flat and
a local complete intersection morphism. -/
@[stacks 06C9]
#check (AlgebraicGeometry.AlgebraicSpace.Syntomic.iff_flat_and_isLocalCompleteIntersection :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Syntomic f ↔ Flat f ∧ IsLocalCompleteIntersection f)
