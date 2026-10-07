module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.Syntomic.Composition

@[expose] public section

/-!
# Syntomic Composition Recall

The two source clauses are owner-level composition laws: one for relative
global complete intersections and one for syntomic ring homomorphisms.

@stack 00SZ
-/

/- Lemma 10.136.17 (1), tag 00SZ: syntomic ring homomorphisms are stable
under composition. -/
@[stacks 00SZ "composition of syntomic ring homomorphisms"]
#check @RingHom.Syntomic.comp

#check @RingHom.Syntomic.stableUnderComposition

/- Lemma 10.136.17 (2), tag 00SZ: relative global complete intersections are
stable under composition. -/
@[stacks 00SZ "composition of relative global complete intersections"]
#check @Algebra.IsRelativeGlobalCompleteIntersection.comp
