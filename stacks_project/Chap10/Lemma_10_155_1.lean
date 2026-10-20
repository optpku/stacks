module

public import ReasLib.RingTheory.Henselian.Henselization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.155.1

@stack 04GN

The reusable owner is `IsHenselizationOf.exists_henselization`. The former chapter-local
closed-etale-neighborhood category was proof scaffolding for this existence
theorem; its data owner is the more general
`PrimeSpectrum.EtaleNeighborhood` in ReasLib.
-/

@[stacks 04GN "existence of henselizations"]
#check @IsHenselizationOf.exists_henselization
