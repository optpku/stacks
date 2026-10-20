module

public import Mathlib.Topology.Sheaves.Sheafify
import StacksCheckRecall

@[expose] public section

/- The canonical lift already packages the factorization morphism, while its factorization and
uniqueness laws are the exact two parts of the source's unique-factorization assertion. Using
these site-level owners keeps the statement reusable beyond topological spaces; specializing
`J` to `Opens.grothendieckTopology X` and the target presheaf to `𝒢.presheaf` recovers the source. -/

/- Lemma 6.17.3 (1): every morphism from a presheaf of sets to a sheaf factors through the
canonical sheafification map. -/
@[stacks 0080 "existence of the factorization through sheafification"]
recall CategoryTheory.toSheafify_sheafifyLift

/- Lemma 6.17.3 (2): the factorization through the canonical sheafification map is unique. -/
@[stacks 0080 "uniqueness of the factorization through sheafification"]
recall CategoryTheory.sheafifyLift_unique
