module

public import ReasLib.RingTheory.RingHom.IndEtale.Henselian.ResiduePoint
import StacksCheckRecall

/-!
# Etale lifting to a strict henselization

@stack 04GT

The reusable owner works for an arbitrary ind-etale algebra and an arbitrary Henselian local
target.  A strict henselization and an etale algebra supply those hypotheses, so the source's
external residue-coordinate statement is a direct specialization.
-/

@[expose] public section

@[stacks 04GT "unique lift in external residue coordinates"]
#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal_residueEquiv
