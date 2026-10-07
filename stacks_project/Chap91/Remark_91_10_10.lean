module

public import stacks_project.Chap91.Remark_91_10_10_Thickening
import StacksCheckRecall

open CategoryTheory
open SheafOfModules.RingedSite


-- After Stacks 08M6 identifies underlying topoi, morphisms of first-order thickenings of a
-- ringed topos are morphisms of same-site projections `πᵢ : O'ᵢ ⟶ O`. The pre-identification
-- packaging is `RingedSite.ToposHom.CommSquare` from 91.9.1.1.

/- Remark 91.10.10 (1): a sequence of morphisms of first-order thickenings of `(Sh(C), O)` is a
complex when the induced `O`-module maps of ideal sheaves `I₃ ⟶ I₂ ⟶ I₁` compose to zero. -/
@[stacks 08ML] #check @FirstOrderThickening.IsComplex

/- Remark 91.10.10 (2): if the sequence is a complex, the composite `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)`
factors uniquely through `(Sh(C), O) ⟶ (Sh(D₃), O'₃)`, so the first-order thickening
`(Sh(D₁), O'₁)` is trivial and comes with a unique canonical trivialization `σ : O ⟶ O'₁`. -/
@[stacks 08ML] #check @FirstOrderThickening.existsUnique_canonicalTrivialization

/- Remark 91.10.10 (3): a sequence of morphisms of first-order thickenings of `(Sh(C), O)` is a
short exact sequence when `0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` is a short exact sequence of `O`-modules. -/
@[stacks 08ML] #check @FirstOrderThickening.IsShortExact
