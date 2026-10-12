/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Homotopy
import StacksCheckRecall

/-!
# Contractibility of the extended alternating Cech complex

@stack 0G6J
-/

@[expose] public section

/- Lemma 15.29.4: if one member of the family is a unit, the extended alternating Cech complex is
homotopy equivalent to zero. -/
@[stacks 0G6J "Lemma 15.29.4"]
#check @LocalizedModule.Away.Cech.Alternating.extended.homotopyEquivalent_zero_of_isUnit_at

#check @LocalizedModule.Away.Cech.Alternating.familyMap.isSplitMono_of_isUnit_at
#check @LocalizedModule.Away.Cech.Alternating.extended.isContractible_of_isUnit_at
#check @LocalizedModule.Away.Cech.Alternating.extended.homotopyEquivalent_zero_of_exists_isUnit
