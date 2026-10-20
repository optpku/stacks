module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
import StacksCheckRecall

/-!
# Lemma 10.71.1

@stack 00LP
-/

@[expose] public section

/- Lemma 10.71.1 (1): every module over a ring admits a resolution by free modules. -/
@[stacks 00LP "(1), free resolution"]
#check @ChainComplex.exists_freeResolution

/- Lemma 10.71.1 (2): a finite module over a Noetherian ring admits a resolution by finite free
modules. -/
@[stacks 00LP "(2), finite free resolution"]
#check @ChainComplex.exists_finiteFreeResolution
