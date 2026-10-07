module

public import stacks_project.Chap96.Definition_96_9_2_Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Definition 96.9.2 (1): let `p : X ⟶ (Sch/S)_fppf` be a category fibred in
groupoids, let `x` lie over `U = p(x)`, and let `F` be a presheaf on `X`.
The pullback `x⁻¹ F` is the restriction of `F` to `X/x`, viewed as a
presheaf on `(Sch/U)_fppf` via the equivalence `X/x ⟶ (Sch/U)_fppf` of
Lemma 96.9.1. The 2-Yoneda 1-morphism of `x` is the chosen quasi-inverse. -/
@[stacks 06W1]
#check GroupoidsOver.pullbackPresheaf

/- Definition 96.9.2 (2): the restriction of `F` to `U_étale` is
`(x⁻¹ F)|_{U_étale}`, abusively written `F|_{U_étale}`. -/
@[stacks 06W1]
#check GroupoidsOver.restrictEtalePresheaf
