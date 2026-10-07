module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Resolution.PrincipalAnnihilator.RightControl

@[expose] public section

/- Lemma 16.7.2 is the source-facing existence view of generic singular
control on a finite common factorisation. -/
@[stacks 07CT]
#check @AlgHom.CommonFactorisation.Finite.RightSingularControl.nonempty_of_exists

#check @AlgHom.CommonFactorisation.Finite.RightSingularControl
#check @AlgHom.CommonFactorisation.Finite.RightSingularControl.nonempty_of_principalAnnihilator
#check @AlgHom.CommonFactorisation.Finite.RightSingularControl.spec
#check @Algebra.PrincipalQuotient.map
#check @Algebra.singularIdeal
#check @AlgHom.singularIdeal
#check @Module.IsTorsionStable
