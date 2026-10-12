/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.AffineOrProjective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.43.10: let `X` be a curve over a field `k`. Then either the underlying scheme
`X.left` is affine or its structure morphism `X.hom` is H-projective over `k`. -/
@[stacks 0A27] #check
  (AlgebraicGeometry.Curve.isAffine_or_hProjective :
    ∀ {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [AlgebraicGeometry.Curve X],
      IsAffine X.left ∨ HProjective X.hom)
