/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.MixedCharacteristic
import StacksCheckRecall

/-!
# Definition 15.114.3: mixed-characteristic DVRs

The repository path retains the legacy chapter numbering.  The canonical mixed-characteristic
predicate, localized-integer extension, and absolute ramification index are owned by ReasLib.

@stack 09EK
-/

@[expose] public section

-- Definition 15.114.3 (1): the canonical mixed-characteristic predicate and its DVR criterion.
@[stacks 09EK "mixed-characteristic criterion for a discrete valuation ring"]
#check @DVR.MixedCharacteristic.mixedCharZero_iff_fractionRing_charZero_and_residueField_charP

-- Definition 15.114.3 (2): the canonical localized-integer map `ℤ_(p) → A`.
@[stacks 09EK "canonical map from the localized integers"]
#check @DVR.MixedCharacteristic.integerPrimeLocalizationMap

-- Definition 15.114.3 (3): the canonical map is an extension of discrete valuation rings.
@[stacks 09EK "mixed-characteristic extension of discrete valuation rings"]
#check @DVR.MixedCharacteristic.integerPrimeLocalizationIsExtension

-- Definition 15.114.3 (4): the absolute ramification index.
@[stacks 09EK "absolute ramification index in mixed characteristic"]
#check @DVR.MixedCharacteristic.absoluteRamificationIndex
