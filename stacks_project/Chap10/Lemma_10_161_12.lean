module

public import ReasLib.RingTheory.Normal.Nagata.PurelyInseparable
import StacksCheckRecall

@[expose] public section

/-!
# Purely Inseparable Tests for Japanese Domains

@stack 032N

This source-facing file recalls the shared positive-characteristic criterion
for Japanese domains.
-/

-- Lemma 10.161.12, tag `032N`: an `N-2` domain in positive characteristic can be tested on
-- finite purely inseparable extensions of its fraction field.
@[stacks 032N]
#check @IsN2Ring.iff_forall_finitePurelyInseparable
