module

public import ReasLib.RingTheory.Smooth.Adic.Completion
import StacksCheckRecall

/-!
# Lemma 15.37.4 (07ED)

@stack 07ED
-/

@[expose] public section

/- Lemma 15.37.4 (07ED): adic formal smoothness is invariant under finitely generated adic
completion in the three source and target forms. -/
@[stacks 07ED]
#check @RingHom.AdicContinuous.formallySmooth_tfae

#check @RingHom.formally_smooth_for_adic_tfae_completion_invariance
