module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.6

This file recalls the finite-free embedding criterion for reflexive modules.

@stack 0AV2
-/

@[expose] public section

/- Lemma 15.23.6: a finite module over a Noetherian domain is reflexive exactly when it embeds in
a finite free module with torsion-free cokernel. -/
@[stacks 0AV2 "Lemma 15.23.6"]
#check @Module.IsReflexive.iff_exists_fin_free_quotient_torsionFree
