module

public import Mathlib.Topology.Category.TopCommRingCat
import StacksCheckRecall

@[expose] public section

universe u

/-
Definition 5.30.7 (1): the source condition that addition and multiplication are continuous is
the canonical mathlib class `IsTopologicalRing`. For rings, continuity of negation follows from
continuity of multiplication by `-1`, so no project-local predicate or equivalence wrapper is
needed.
-/
@[stacks 0B22 "topological rings via continuous addition and multiplication"]
#check IsTopologicalRing

section

variable {R S : Type u} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
variable [IsTopologicalRing R] [IsTopologicalRing S]

/-
Definition 5.30.7 (2): `TopCommRingCat` is the canonical bundled owner whose morphisms are ring
homomorphisms equipped with continuity, so the displayed hom type exactly realizes homomorphisms
of topological rings without introducing a parallel map structure.
-/
@[stacks 0B22 "continuous ring homomorphisms between topological rings"]
#check (TopCommRingCat.of R ⟶ TopCommRingCat.of S)

end
