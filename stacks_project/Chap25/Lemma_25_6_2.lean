/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Augmentation
import StacksCheckRecall

/-!
# Degree-zero cohomology of a presheaf-target hypercovering

The sections functor, augmented zero-degree fork, and cohomology identification are owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Augmentation`.
-/

/- Lemma 25.6.2 [stacks 09VV]: the degree-zero Cech cohomology of a hypercovering of a
presheaf is canonically isomorphic to the sections of the target presheaf. -/
@[stacks 09VV] #check
  @CategoryTheory.HypercoveringOf.Cech.cohomology_zero_isomorphic_targetSections

#check @CategoryTheory.HypercoveringOf.Cech.targetSections
#check @CategoryTheory.HypercoveringOf.Cech.augmentationMap
#check @CategoryTheory.HypercoveringOf.Cech.faceMap
#check @CategoryTheory.HypercoveringOf.Cech.zeroFork
