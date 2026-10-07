module

public import ReasLib.RingTheory.GenericFlatness.Locus.Away
import StacksCheckRecall

@[expose] public section

/-!
# The Good Locus under Principal Localization

The source equality is recalled in the basic-open coordinates used by the
identification `Spec(R_f) = D(f)`.

@stack 051X
-/

/- Lemma 10.118.5: under `Spec(R_f) = D(f)`, the good locus of the localized
algebra-module pair is the restriction of the original good locus to `D(f)`. -/
@[stacks 051X]
#check @GenericFlatness.goodLocusAway_image_eq_restrict
