/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.End.Power
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 20.39.2

The source-facing entry is a recall block for the representation-independent endomorphism-power
owner.  Kernels, quotient rows, two-term complexes, and their canonical augmentation are defined
in `CategoryTheory.End.Power`; this chapter file deliberately adds no competing data owner.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.End.Power

/- Lemma 20.39.2 (0H3D): if the kernels of the positive powers of an endomorphism stabilize, the
canonical cokernel augmentation of the quotient tower and the two-term tower is a pro-isomorphism. -/
@[stacks 0H3D]
#check @CategoryTheory.End.Power.augmentation_isIso

/- The fixed-shift inverse data underlying the pro-isomorphism. -/
@[stacks 0H3D]
#check @CategoryTheory.End.Power.existsShiftInverse

/- The source objects and transitions are exposed through the reusable system API. -/
@[stacks 0H3D]
#check @CategoryTheory.End.Power.kernelStabilizes
@[stacks 0H3D]
#check @CategoryTheory.End.Power.cokernelSystem
@[stacks 0H3D]
#check @CategoryTheory.End.Power.twoTermSystem
@[stacks 0H3D]
#check @CategoryTheory.End.Power.augmentationSystem

end
