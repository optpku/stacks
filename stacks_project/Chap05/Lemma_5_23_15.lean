module

public import ReasLib.Topology.IrreducibleCloseds.Soberification.Properties
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.15 (1): the irreducible-closed soberification of a compact space
is compact. -/
@[stacks 0A2T "compact soberification"]
#check IrreducibleCloseds.compactSpaceSoberification

/- Lemma 5.23.15 (2): the irreducible-closed soberification of a compact
prespectral quasi-separated space is spectral. -/
@[stacks 0A2T "spectral soberification"]
#check IrreducibleCloseds.spectralSpaceSoberification

/- Lemma 5.23.15 (3): the irreducible-closed soberification of a Noetherian
space is Noetherian. -/
@[stacks 0A2T "Noetherian soberification"]
#check IrreducibleCloseds.noetherianSpaceSoberification
