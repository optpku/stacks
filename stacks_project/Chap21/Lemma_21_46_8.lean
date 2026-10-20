/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Retracts
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.46.8

Retract stability and the binary-biproduct API for Tor-amplitude are owned by the generic
`DerivedTensor.TorAmplitude` library; this file is only the tagged Chapter 21 source entry.
-/

/- Lemma 21.46.8 (08G3): if a binary biproduct has Tor-amplitude in `[a, b]`, then both
summands have Tor-amplitude in `[a, b]`. -/
@[stacks 08G3]
#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.summands_of_biprod

#check @CategoryTheory.DerivedCategory.DerivedTensor.torAmplitudeGE_isStableUnderRetracts
#check @CategoryTheory.DerivedCategory.DerivedTensor.torAmplitudeLE_isStableUnderRetracts
#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.left_of_biprod
#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.right_of_biprod

end
