/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.FiberDimension
import StacksCheckRecall

@[expose] public section

/- Lemma 35.33.8: for `d : ℕ∞`, having local fibre dimension `d` is étale local on the
source-and-target for morphisms of scheme germs. -/
@[stacks 04NL] #check
  (AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberDimensionEq_isEtaleLocal :
    ∀ d : ℕ∞, AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal
      (AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberDimensionEq d))
