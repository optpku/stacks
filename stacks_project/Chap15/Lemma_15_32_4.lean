module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.KoszulRegular.FaithfullyFlat
public import ReasLib.RingTheory.Ideal.Regularity.FaithfullyFlat
public import ReasLib.RingTheory.Ideal.QuasiRegular.FaithfullyFlat

/-!
# Lemma 15.32.4

@stack 068N
-/

@[expose] public section

/-!
# Faithfully-Flat Descent of Regular Ideals Recall

The three local ideal conditions have separate owner leaves, so a consumer can
import only the descent theorem at the level it uses.
-/

/- Lemma 15.32.4 (1), tag 068N: Koszul-regularity descends along faithfully
flat ring maps. -/
@[stacks 068N "faithfully flat descent of Koszul-regular ideals"]
#check @Ideal.IsKoszulRegularIdeal.of_faithfullyFlat

/- Lemma 15.32.4 (2), tag 068N: `H_1`-regularity descends along faithfully
flat ring maps. -/
@[stacks 068N "faithfully flat descent of H1-regular ideals"]
#check @Ideal.IsH1RegularIdeal.of_faithfullyFlat

/- Lemma 15.32.4 (3), tag 068N: quasi-regularity descends along faithfully
flat ring maps. -/
@[stacks 068N "faithfully flat descent of quasi-regular ideals"]
#check @Ideal.IsQuasiRegularIdeal.of_faithfullyFlat
