module

public import ReasLib.RingTheory.LocalRing.ResidueField.FlatExtension
import StacksCheckRecall

/-!
# Flat local residue-field extensions

@stack 03C3

The transfinite construction used in the source proof is not a stable
downstream API.  The ReasLib producer keeps the actual ring, local map,
flatness, maximal-ideal equality, and residue-field equivalence explicit.
-/

@[expose] public section

@[stacks 03C3 "source bridge"]
#check @IsLocalRing.ResidueField.exists_flat_localExtension
