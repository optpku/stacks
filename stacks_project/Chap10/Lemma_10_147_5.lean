module

public import ReasLib.RingTheory.RingHom.IndSmooth.IntegralClosure
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.147.5: Let `R → S` and `R → B` be ring maps, let `A` and `A'` be the respective
integral closures, and assume that `S` is a filtered colimit of smooth `R`-algebras.  The
canonical map `S ⊗[R] A → A'` is an isomorphism, recalled here through its bijectivity.

@stack 0CBF
-/

@[stacks 0CBF "canonical comparison map"]
#check @TensorProduct.toIntegralClosure

@[stacks 0CBF "ind-smooth base change"]
#check @TensorProduct.toIntegralClosure_bijective_of_indSmooth
