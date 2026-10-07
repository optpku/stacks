module

public import ReasLib.RingTheory.Normal.Nagata.PowerSeries
import StacksCheckRecall

@[expose] public section

/-!
# N-2 Power Series Rings

@stack 032Q

This chapter item is a source-facing recall of the reusable N-2 power-series
permanence API.
-/

-- Lemma 10.161.17, tag `032Q`: a one-variable formal power-series ring over a
-- Noetherian `N-2` domain is `N-2`.
@[stacks 032Q]
#check @IsN2Ring.powerSeries
