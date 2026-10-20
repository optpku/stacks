module

public import ReasLib.RingTheory.RingHom.IndEtale.Henselian.ResiduePoint
import StacksCheckRecall

@[expose] public section

/-!
# Ind-etale residue-point lifting

@stack 08HR

Lemma 10.154.6 is a source-facing recall of the neutral
`RingHom.IndEtale.ResiduePoint` bridge.  Its canonical owner is still
`RingHom.IndEtale.existsUnique_lift`; the ideal presentation is kept in the
shared leaf because it is useful outside this chapter.  The ordinary
`RingHom.IndEtale` forms are primary; arbitrary-presentation forms are named
explicitly with `_ofRaw`.
-/

/- Lemma 10.154.6 (tag `08HR`): an ind-etale algebra has a unique lift to a
Henselian local algebra with a prescribed compatible residue-field point. -/
@[stacks 08HR]
#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal

#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal_ofRaw
#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal_residueMap
#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal_residueMap_ofRaw
#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal_residueEquiv
#check @RingHom.IndEtale.ResiduePoint.existsUnique_lift_ofIdeal_residueEquiv_ofRaw
#check @RingHom.IndEtale.existsUnique_lift
#check @RingHom.IndEtale.existsUnique_lift_ofRaw
