module

public import ReasLib.LinearAlgebra.UniversallyInjective.Projective.TFAE
import StacksCheckRecall

/-!
# Lemma 15.15.4

@stack 05GQ
-/

@[expose] public section

/- Lemma 15.15.4: the five annihilator, universal-injectivity, projective-cokernel,
complemented-submodule, and split-injection conditions are equivalent. -/
@[stacks 05GQ "Lemma 15.15.4"]
#check @LinearMap.UniversallyInjective.properFGIdealAnnihilator_tfae

#check @LinearMap.UniversallyInjective
