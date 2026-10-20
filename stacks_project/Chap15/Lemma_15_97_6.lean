module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.BaseChange.Principal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.97.6

@stack 0F7X
-/

/-!
# Lemma 15.97.6

The statement is attached to the canonical eta base-change comparison.  ReasLib also exposes a
stronger companion without the global boundedness hypothesis and a degreewise bijectivity API.
-/

-- Lemma 15.97.6: the canonical eta base-change comparison is an isomorphism.
@[stacks 0F7X "base change for the Berthelot-Ogus eta complex"]
#check @CochainComplex.BerthelotOgus.Int.BaseChange.comparison_isIso

-- Generalized comparison and degreewise forms for downstream use.
#check @CochainComplex.BerthelotOgus.Int.BaseChange.comparison_isIso_of_isPrincipal
#check @CochainComplex.BerthelotOgus.Int.BaseChange.termLinear_bijective_of_isPrincipal
