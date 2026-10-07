module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.SupportDim
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.62.6

@stack 00L8
-/

/- Lemma 10.62.6: if `R` is a Noetherian local ring and `M` is a finite `R`-module, then the
invariant `d(M)` from Definition 10.59.8 equals the Krull dimension of `Supp(M)`, written
canonically via the lifted owner map `Nat.castOrderEmbedding.withBotMap`. -/
@[stacks 00L8]
#check @Ideal.HilbertSamuel.map_degree_eq_supportDim
