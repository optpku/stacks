/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Hypercovering
import StacksCheckRecall

/-!
# Remark 25.8.4

The reusable relative hypercovering owner with source label `0DER` is
`ReasLib.CategoryTheory.MorphismProperty.Hypercovering`.
-/

/- Remark 25.8.4 (0DER): a morphism property defines a relative hypercovering condition. -/
@[stacks 0DER] #check @CategoryTheory.MorphismProperty.Hypercovering

/- Stable multiplicative morphism properties contain all augmentations and face maps of such a
relative hypercovering. -/
#check @CategoryTheory.MorphismProperty.Hypercovering.augmentation_mem
#check @CategoryTheory.MorphismProperty.Hypercovering.faceMap_mem
