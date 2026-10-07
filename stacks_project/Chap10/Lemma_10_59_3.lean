module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Exact
import StacksCheckRecall

/-!
# Lemma 10.59.3

@stack 00K6
-/

@[expose] public section

/- Lemma 10.59.3 (Stacks 00K6): one finite-colength submodule and one shift
simultaneously give the `χ`- and `φ`-decompositions for a short exact
sequence. -/
@[stacks 00K6]
#check @Ideal.HilbertSamuel.ShortExact.exists_decomposition

@[stacks 00K6 "chi decomposition"]
#check @Ideal.HilbertSamuel.ShortExact.exists_chi_decomposition

@[stacks 00K6 "phi decomposition"]
#check @Ideal.HilbertSamuel.ShortExact.exists_phi_decomposition
