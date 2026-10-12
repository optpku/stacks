/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification
import StacksCheckRecall

universe u v

/- Definition 37.73.1: an affine stratification of a scheme is a locally finite stratification
by affine strata whose canonical inclusion morphisms into the ambient scheme are affine. -/
@[stacks 0F2S] #check
  (AlgebraicGeometry.Scheme.IsAffineStratification :
    {X : AlgebraicGeometry.Scheme.{u}} → {I : Type v} → [PartialOrder I] →
      (I → Set X) → Prop)
