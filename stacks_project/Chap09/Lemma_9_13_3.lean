module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import StacksCheckRecall

@[expose] public section

/-!
Lemma 9.13.3 (Tag 0CKM) is the canonical linear independence theorem for algebra homomorphisms,
whose source-field specialization follows by restricting the indexed family.
-/

@[stacks 0CKM]
#check linearIndependent_algHom_toLinearMap
