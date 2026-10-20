module

public import ReasLib.Algebra.Module.Length.ResidueField
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.52.6

@stack 00IY

The owner predicate `Module.IsTorsionBySet R M m` packages the source
hypothesis `m • M = 0` and supplies the canonical residue-field module
structure. The first recall identifies those hypotheses; the remaining two
are the source conclusions without chapter-level aliases or public `letI`
plumbing.
-/

@[stacks 00IY "annihilation and torsion-by-set criterion"]
#check @Module.isTorsionBySet_iff_smul_top_eq_bot

@[stacks 00IY "(1), length as residue-field rank"]
#check @Module.length_eq_rank_quotient_of_isTorsionBySet

@[stacks 00IY "(2), finite-length criterion"]
#check @Module.isFiniteLength_iff_finite_of_isTorsionBySet
