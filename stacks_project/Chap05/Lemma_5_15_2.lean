module

public import Mathlib.Topology.Constructible
import StacksCheckRecall

@[expose] public section

/-
The source needs closure under arbitrary finite families. The verified canonical candidates are
`Topology.IsConstructible.iInter` and `.iUnion` for finite indexed families,
`Topology.IsConstructible.sInter` and `.sUnion` for finite sets of sets, and
`Topology.IsConstructible.compl`. The indexed forms state the closure operation directly, include
empty families through `[Finite ι]`, and recover the finite-set presentation by indexing its
members. They retain exactly an arbitrary topological space and a finite index type, with no
separation assumption, and give later indexed constructions a directly reusable API.
-/

/- Lemma 5.15.2 (1): a finite intersection of constructible subsets is constructible. -/
@[stacks 005H "finite intersections of constructible subsets"]
#check Topology.IsConstructible.iInter

/- Lemma 5.15.2 (2): a finite union of constructible subsets is constructible. -/
@[stacks 005H "finite unions of constructible subsets"]
#check Topology.IsConstructible.iUnion

/- Lemma 5.15.2 (3): the complement of a constructible subset is constructible. -/
@[stacks 005H "complements of constructible subsets"]
#check Topology.IsConstructible.compl
