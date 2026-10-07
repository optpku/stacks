module

public import ReasLib.Topology.Sheaves.Algebraic.Sheafification
import StacksCheckRecall

@[expose] public section

/- Lemma 6.19.1: a presheaf with values in a type of algebraic structure admits a sheafification
whose underlying presheaf of sets is the ordinary sheafification, and maps to sheaves factor
uniquely through it. -/
@[stacks 0087]
#check TopCat.Presheaf.existsSheafificationOfIsAlgebraicStructure
