module

public import ReasLib.Algebra.Module.Flat.BaseChange
import StacksCheckRecall

/-!
# Lemma 10.39.9

@stack 0584
-/

@[expose] public section

/- Lemma 10.39.9 (1), in canonical module form: if `S'` is flat over `S` and `M` is flat over
`R`, then `S' ⊗[S] M` is flat over `R`. -/
@[stacks 0584 "flat base change"]
#check @Module.Flat.baseChange_of_flat

/- Lemma 10.39.9 (2), in canonical module form: if `S'` is faithfully flat over `S`, then an
`S`-module `M` is flat over `R` if and only if its base change `S' ⊗[S] M` is flat over `R`. -/
@[stacks 0584 "faithfully flat base change"]
#check @Module.Flat.iff_baseChange_of_faithfullyFlat

#check @Module.Flat.lTensor_exact
#check @Module.FaithfullyFlat.lTensor_reflects_exact
