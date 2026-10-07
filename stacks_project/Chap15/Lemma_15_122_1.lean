module

public import ReasLib.RingTheory.PicardGroup.RegularLocal
import StacksCheckRecall

/-!
# Lemma 15.122.1 (0AFZ)

@stack 0AFZ

The principal-localization Picard theorem is owned by the regular-local
Picard-group leaf.  This chapter entry is its direct source recall.
-/

@[expose] public section

/- Lemma 15.122.1 (0AFZ): `Pic(R_f) = 0` for a regular local ring. -/
@[stacks 0AFZ "Lemma 15.122.1: trivial Picard group after principal localization"]
#check @IsRegularLocalRing.subsingletonPicardGroup_localizationAway

#check @IsRegularLocalRing.uniqueFactorizationMonoid

#print axioms IsRegularLocalRing.subsingletonPicardGroup_localizationAway
