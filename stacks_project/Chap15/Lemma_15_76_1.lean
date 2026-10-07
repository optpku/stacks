module

public import ReasLib.Algebra.Homology.CochainComplex.Acyclic.LiftModIdeal
import StacksCheckRecall

/-!
# Bounded-above acyclic lifting modulo an ideal

The reusable lifting theorem and quotient-module comparison API for Lemma 15.76.1 are owned by
`ReasLib.Algebra.Homology.CochainComplex.Acyclic.LiftModIdeal`.

@stack 0BC9
-/

@[expose] public section

/- Lemma 15.76.1 (0BC9): a bounded-above acyclic complex modulo an ideal whose terms lift from
a projective class closed under complementary direct summands has a bounded-above acyclic lift. -/
@[stacks 0BC9 "bounded-above acyclic lifting modulo an ideal"]
#check @CochainComplex.Minus.TermsIn.existsAcyclicLiftModIdeal

#check @CochainComplex.Minus.TermsIn.existsAcyclicLiftModIdeal_of_retracts
#check @CochainComplex.Minus.TermsIn.existsTermLiftModIdeal
#check @ModuleCat.ModIdeal.extensionIso
#check @ModuleCat.ModIdeal.extensionIso_naturality
#check @ModuleCat.ModIdeal.extension_map_surjective_iff
