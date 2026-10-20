module

public import ReasLib.RingTheory.RingHom.IndEtale.Henselian.ResiduePoint
import StacksCheckRecall

@[expose] public section

/-!
# Etale lifting to henselian local rings

The ideal/residue-map formulation is owned directly by the ReasLib residue
point leaf.  Etale maps enter through the canonical `IndEtale.ofEtale` bridge.

@stack 08HQ
-/

@[stacks 08HQ "ideal residue-map lift"]
#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal_residueMap

@[stacks 08HQ "etale-to-ind-etale bridge"]
#check @RingHom.IndEtale.ofEtale
