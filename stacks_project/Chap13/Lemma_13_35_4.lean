/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Extension
import StacksCheckRecall

@[expose] public section

-- Lemma 13.35.4: additive extension stages are owned by the neutral pretriangulated API.
@[stacks 0FX4] #check @CategoryTheory.ObjectProperty.additiveExtensionStageNat

@[stacks 0FX4] #check @CategoryTheory.ObjectProperty.additiveExtensionStage

@[stacks 0FX4] #check @CategoryTheory.ObjectProperty.additiveExtensionStage_monotone

@[stacks 0FX4] #check @CategoryTheory.ObjectProperty.additiveExtensionStage_one

@[stacks 0FX4] #check @CategoryTheory.ObjectProperty.additiveExtensionStageNat_succ_add

@[stacks 0FX4] #check @CategoryTheory.ObjectProperty.additiveExtensionStage_add
