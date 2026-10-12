/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Affine
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsAffine X] [IsAffine S]

/- Lemma 37.6.6: For a morphism of affine schemes, formal unramifiedness is equivalent
to formal unramifiedness of the induced map on global sections. -/
@[stacks 02HD] #check
  (AlgebraicGeometry.FormallyUnramified.iff_of_isAffine (f := f) :
    AlgebraicGeometry.FormallyUnramified f ↔ f.appTop.hom.FormallyUnramified)
