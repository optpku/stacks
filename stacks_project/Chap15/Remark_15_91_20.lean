/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleProperties
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Regular
import StacksCheckRecall

/-!
# The scope of the Beauville--Laszlo theorem

The classical setup takes the target ring to be the principal-adic
completion and the distinguished element to be a nonzerodivisor.  The
canonical ReasLib owners also cover glueable modules with power torsion and
the flatness and finite-projectivity criteria for modules that need not be
glueable.

@stack 0BP8
-/

/- Remark 15.91.20 (0BP8): a nonzerodivisor and its principal-adic completion
form a Beauville--Laszlo glueing pair. -/
@[stacks 0BP8 "regular principal-adic Beauville-Laszlo glueing pair"]
#check @LocalizedModule.Away.BeauvilleLaszlo.principalAdicCompletion_isGlueingPair_of_mem_nonZeroDivisors

/- Theorem 15.91.16 supplies the equivalence for every module glueable along
the pair, including glueable modules with principal-power torsion. -/
@[stacks 0BP8 "Beauville-Laszlo equivalence beyond torsion-free modules"]
#check @LocalizedModule.Away.FormalGluing.Single.glueableFunctor_isEquivalence

/- Lemma 15.91.10 identifies glueability with injectivity on principal-power
torsion for a glueing pair. -/
@[stacks 0BP8 "module glueability criterion"]
#check @isBeauvilleLaszloGlueableAlong_iff_injective_fPowerTorsionToTensor_of_glueingPair

/- Lemma 15.91.19 detects finite projectivity without assuming that the
module itself is glueable. -/
@[stacks 0BP8 "finite projectivity without a glueability hypothesis"]
#check @LocalizedModule.Away.BeauvilleLaszlo.finiteProjective_iff_baseChange_and_localizedAway_of_glueingPair
