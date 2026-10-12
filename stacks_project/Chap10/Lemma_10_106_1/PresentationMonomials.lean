/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Presentation
public import ReasLib.RingTheory.RegularLocalRing.AssociatedGraded
import StacksCheckRecall

/-!
# Polynomial Presentation Support for Lemma 10.106.1

The canonical polynomial map is owned for an arbitrary ideal and generator
family by `Ideal.AssociatedGraded.Presentation`; regularity enters only through
the theorem that this map is bijective.

@stack 00NO
-/

@[expose] public section

@[stacks 00NO "associated-graded polynomial presentation"]
#check @Ideal.AssociatedGraded.Presentation.map

@[stacks 00NO "images of presentation variables"]
#check @Ideal.AssociatedGraded.Presentation.map_X

@[stacks 00NO "presentation coefficient map"]
#check @Ideal.AssociatedGraded.Presentation.map_C

@[stacks 00NO "generation gives a surjective associated-graded presentation"]
#check @Ideal.AssociatedGraded.Presentation.map_surjective

#check @Ideal.AssociatedGraded.Presentation.map_bijective_iff_injective

@[stacks 00NO "regular-parameter presentation is bijective"]
#check @IsLocalRing.IsRegularSystemOfParameters.associatedGradedMap_bijective
