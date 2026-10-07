module

public import ReasLib.RingTheory.Normal.Nagata.CharZero
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.161.11

@stack 032M

The characteristic-zero equivalence between `N-1` and `N-2` is reusable
normalization infrastructure, owned by `ReasLib`.
-/

/- Lemma 10.161.11, tag `032M`: A Noetherian domain whose fraction field has
characteristic zero is `N-1` if and only if it is `N-2`, i.e. Japanese. -/
@[stacks 032M]
#check @IsN1Ring.iff_isN2Ring_of_fractionRingCharZero
