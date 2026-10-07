module

public import ReasLib.Topology.Maps.Spectral
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.7 (1): a continuous image of a quasi-compact space is quasi-compact. -/
@[stacks 04Z9 "continuous images of quasi-compact spaces are quasi-compact"]
#check @isCompact_range

/- Lemma 5.12.7 (2): the image of a quasi-compact map is retrocompact. This is the range API
for Mathlib's canonical `IsSpectralMap` predicate. -/
@[stacks 04Z9 "images of quasi-compact maps are retrocompact"]
#check @IsSpectralMap.isRetrocompact_range
