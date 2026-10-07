module

public import ReasLib.Topology.Sheaves.OpenCover.Morphisms
import StacksCheckRecall

@[expose] public section

/- Lemma 6.33.1: compatible morphisms between the restrictions of two sheaves of sets to the
members of an open cover glue uniquely to a global morphism. The textbook's `Type`-valued
formulation is the specialization of the canonical coefficient-generic local-Hom theorem; its
overlap comparison uses the standard open-embedding restriction model rather than a parallel
`TopCat.Sheaf.pullback` presentation. -/
@[stacks 04TN]
recall TopCat.Sheaf.OpenCover.LocalHom.existsUniqueGlobalHom
