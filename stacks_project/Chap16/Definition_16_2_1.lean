/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.SingularLocus
import ReasLib.RingTheory.Smooth.SingularLocus.Localization

@[expose] public section

/-!
# Definition 16.2.1 compatibility entry point

The nonsmooth-locus and singular-ideal API is maintained by
`ReasLib.RingTheory.Smooth.SingularLocus`.
-/

/- Definition 16.2.1: the singular ideal is the radical ideal cutting out the
nonsmooth locus. -/
@[stacks 07C5] #check @Algebra.singularIdeal

#check @Algebra.singularIdeal_isRadical
#check @Algebra.zeroLocus_singularIdeal
#check @Algebra.singularIdeal_unique
#check @Algebra.SingularIdeal.mem_iff_smoothAway
#check @Algebra.SingularIdeal.eq_top_iff_smooth
