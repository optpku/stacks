/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Lemma 21.28.1

The unit/counit isomorphism loci and their restricted adjunction are reusable
ReasLib infrastructure.  This chapter entry is a source-facing recall only.
-/

/- Lemma 21.28.1 (0D7Q): for an adjunction `F ⊣ G`, the unit and counit isomorphism loci are
replete, stable under retracts, and triangulated when the adjunction is triangulated. -/
@[stacks 0D7Q]
#check @Adjunction.unitIsoProperty

@[stacks 0D7Q]
#check @Adjunction.counitIsoProperty

#check @Adjunction.unitIsoProperty_isClosedUnderIsomorphisms
#check @Adjunction.counitIsoProperty_isClosedUnderIsomorphisms
#check @Adjunction.unitIsoProperty_isStableUnderRetracts
#check @Adjunction.counitIsoProperty_isStableUnderRetracts
#check @Adjunction.unitIsoProperty_isTriangulated
#check @Adjunction.counitIsoProperty_isTriangulated

@[stacks 0D7Q]
#check @Adjunction.unitIsoProperty_le_counitIsoProperty_inverseImage

@[stacks 0D7Q]
#check @Adjunction.counitIsoProperty_le_unitIsoProperty_inverseImage

@[stacks 0D7Q]
#check @Adjunction.leftRestriction

@[stacks 0D7Q]
#check @Adjunction.rightRestriction

@[stacks 0D7Q]
#check @Adjunction.restrictedAdjunction

@[stacks 0D7Q]
#check @Adjunction.leftAdjoint_fullyFaithful

@[stacks 0D7Q]
#check @Adjunction.rightAdjoint_fullyFaithful

@[stacks 0D7Q]
#check @Adjunction.leftAdjoint_map_bijective

@[stacks 0D7Q]
#check @Adjunction.rightAdjoint_map_bijective

end
