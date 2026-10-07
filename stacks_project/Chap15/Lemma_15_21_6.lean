module

public import ReasLib.RingTheory.Flatness.Integral

import StacksCheckRecall

/-!
# Flatness descent along an integral map

Lemma 15.21.6 descends flatness of a finitely presented polynomial module along an injective
integral ring map.

@stack 0534
-/

@[expose] public section

/- Lemma 15.21.6: if `R ⟶ S` is injective and integral, `M` is finitely presented over
`R[x_1, ..., x_n]`, and `S ⊗[R] M` is flat over `S`, then `M` is flat over `R`. -/
@[stacks 0534 "Lemma 15.21.6"]
#check @Module.Flat.Integral.of_finitePresentation_mvPolynomial
