module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

/- Lemma 26.17.6: open immersions, closed immersions, and immersions are
stable under base change; the closed case pulls back its kernel ideal. -/
@[stacks 01JU] #check IsClosedImmersion.isStableUnderBaseChange
@[stacks 01JU] #check Scheme.Hom.kernelIdealSubobject_pullback_snd
#check Scheme.IdealSheafData.toSubobject_comap
@[stacks 01JU] #check isOpenImmersion_stableUnderBaseChange
@[stacks 01JU] #check IsImmersion.isStableUnderBaseChange
@[stacks 01JU] #check Scheme.Hom.ker_pullback_snd
