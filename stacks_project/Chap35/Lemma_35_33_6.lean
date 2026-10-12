/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.FiberStalkDimension
import StacksCheckRecall

/- Lemma 35.33.6: For `d : ℕ∞`, the property that the local ring of the fibre at the
distinguished source point has Krull dimension `d` is étale local on source and target. -/
@[stacks 04NJ]
#check
  (AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberStalkKrullDimEq_isEtaleLocal :
    ∀ d : ℕ∞,
      AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal
        (AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberStalkKrullDimEq d))
