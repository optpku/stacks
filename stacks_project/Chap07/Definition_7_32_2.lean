module

public import Mathlib.CategoryTheory.Sites.Point.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory GrothendieckTopology

/- Definition 7.32.2: a point of a site C is a functor u : C ⥤ Type such that
covering families are jointly surjective on u, covering pullback comparisons
u(Uᵢ ×_U V) → u(Uᵢ) ×_{u(U)} u(V) are bijective, and the stalk functor
Sh(C) ⥤ Type, F ↦ F_p is left exact.

The canonical owner is the SGA 4 IV 6.3 fiber functor `GrothendieckTopology.Point`:
a functor `fiber : C ⥤ Type w` whose category of elements is cofiltered and
initially small, and which is jointly surjective on covering sieves. Source
clause (1) is `Point.jointly_surjective`. Clause (2) is recovered by cofiltered
`fiber.Elements` (and left-exactness of `fiber` when finite limits exist), not
copied as a covering-only pullback-bijectivity axiom. Clause (3) is the stalk
functor `Point.sheafFiber` together with its `PreservesFiniteLimits` instance.
This is a sufficient model of the three Stacks axioms; the converse is not
claimed. -/
@[stacks 00Y5] #check @GrothendieckTopology.Point

#check @GrothendieckTopology.Point.fiber
#check @GrothendieckTopology.Point.jointly_surjective
#check @GrothendieckTopology.Point.sheafFiber
