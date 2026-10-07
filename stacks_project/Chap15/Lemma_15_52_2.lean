module

public import ReasLib.RingTheory.Excellent.EssentialFiniteness
import StacksCheckRecall

/-!
# Lemma 15.52.2

@stack 07QU
-/

@[expose] public section

/- Lemma 15.52.2 (1): a localization of a finite type algebra over a quasi-excellent ring is
quasi-excellent. This is the essentially-finite-type permanence theorem. -/
@[stacks 07QU "(1)"]
#check @IsQuasiExcellentRing.of_essFiniteType

/- Lemma 15.52.2 (2): a localization of a finite type algebra over an excellent ring is
excellent. This is the essentially-finite-type permanence theorem. -/
@[stacks 07QU "(2)"]
#check @IsExcellentRing.of_essFiniteType
