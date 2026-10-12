/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Affine
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 37.81.2: if the canonical morphism `X.toSpecΓ` admits a retraction,
then `X` is an affine scheme. -/
@[stacks 0H2Q] #check
  (AlgebraicGeometry.Scheme.isAffine_of_isSplitMono_toSpecΓ :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [CategoryTheory.IsSplitMono X.toSpecΓ],
      AlgebraicGeometry.IsAffine X)
