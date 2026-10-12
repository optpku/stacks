/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Alternating
import StacksCheckRecall

/-!
# The extended alternating Cech complex

@stack 0G6G
-/

@[expose] public section

/- Lemma 15.29.1: the extended alternating Cech complex is the augmentation of the ordinary
alternating Cech complex associated to the principal-localization family. -/
@[stacks 0G6G "Lemma 15.29.1"]
#check @LocalizedModule.Away.Cech.Alternating.extended

#check @LocalizedModule.Away.Cech.Alternating.complex
#check @LocalizedModule.Away.Cech.Alternating.augmentation
#check @LocalizedModule.Away.Cech.Alternating.augmentationMap
