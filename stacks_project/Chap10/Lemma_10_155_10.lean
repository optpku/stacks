module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Comparison
import StacksCheckRecall

@[expose] public section

/-!
# Comparison of strict henselizations

The reusable owner is the coordinate-square comparison API in
`IsStrictHenselizationOf.Comparison`.  Chosen separable closures are external
coordinates, and the bridge to native residue-field compatibility is internal
to that shared owner.

@stack 04GU
-/

/- Lemma 10.155.10 (tag `04GU`): chosen residue-field equivalences, their
source and target coordinate equations, and a commuting map between the
external fields determine a unique local comparison of strict henselizations.
The shared coordinate-square owner preserves this source-facing formulation
without making the fields or equivalences global data. -/
@[stacks 04GU]
#check @IsStrictHenselizationOf.Comparison.existsUnique_ofCoordinateSquare
