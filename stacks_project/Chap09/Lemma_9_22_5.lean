module

public import ReasLib.FieldTheory.Galois.KrullTopology.Tower
import StacksCheckRecall

@[expose] public section

/- Lemma 9.22.5 (Tag 0BMM): the inclusion and restriction maps in a Galois tower form a short
exact sequence of profinite topological groups. -/
@[stacks 0BMM]
#check FieldExtension.galoisTowerIsShortExact
