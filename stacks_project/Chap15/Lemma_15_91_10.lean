module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCriterion

import StacksCheckRecall

/-!
# The module Beauville-Laszlo criterion

The right-, left-, and middle-exactness criteria and their glueability consequences are owned by
`ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCriterion`.

@stack 0BNW
-/

-- Lemma 15.91.10 (1): right exactness.
@[stacks 0BNW "Lemma 15.91.10 (1)"]
#check @beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective

-- Lemma 15.91.10 (2): left exactness and injectivity on power torsion.
@[stacks 0BNW "Lemma 15.91.10 (2)"]
#check @beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective

-- Lemma 15.91.10 (3): middle exactness and surjectivity on power torsion.
@[stacks 0BNW "Lemma 15.91.10 (3)"]
#check @beauvilleLaszloModuleCech_exact_iff_fPowerTorsionToTensor_surjective

-- Lemma 15.91.10 (4): the bijective power-torsion criterion.
@[stacks 0BNW "Lemma 15.91.10 (4)"]
#check @isBeauvilleLaszloGlueableAlong_iff_bijective_fPowerTorsionToTensor

-- Lemma 15.91.10 (5): the injective criterion for a glueing pair.
@[stacks 0BNW "Lemma 15.91.10 (5)"]
#check @isBeauvilleLaszloGlueableAlong_iff_injective_fPowerTorsionToTensor_of_glueingPair

-- Lemma 15.91.10 (6): principal-adic completion specialization.
@[stacks 0BNW "Lemma 15.91.10 (6)"]
#check @isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair
