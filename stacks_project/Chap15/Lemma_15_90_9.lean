module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.FormalGluing.Exact
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.90.9 (05EK)

@stack 05EK
-/

-- Lemma 15.90.9: flat formal gluing with unchanged quotient gives an exact module complex.
@[stacks 05EK "Lemma 15.90.9"]
#check @LocalizedModule.Away.Cech.FormalGluing.complex_exact_of_flat_of_quotientMap_bijective
