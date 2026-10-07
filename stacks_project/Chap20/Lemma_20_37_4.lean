module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Single

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Single

/-
Lemma 20.37.4: let `(F_n)` be a sequential inverse system of `𝒪_X`-modules.  Suppose that every
stage is acyclic on a basis `𝓑` and that `R¹ lim F_n(U) = 0` for every `U ∈ 𝓑`.  Then the
degree-zero object on `lim F_n` is a derived limit of the degree-zero tower, and its positive
cohomology on every member of `𝓑` vanishes.

The reusable owner separates the two hypotheses, exposes their expanded source formulations, and
uses the Prop-valued `HomotopyLimit.IsOf` as its canonical conclusion.  A
`Nonempty (IsDerivedLimit ...)` bridge remains available for legacy consumers that need a
presentation.
-/

@[stacks 0BKS "Lemma 20.37.4 (1): the ordinary limit computes the derived limit"]
#check @isOf

@[stacks 0BKS "Lemma 20.37.4 (2): higher cohomology of the limit vanishes on the basis"]
#check @higherCohomologyIsZero

@[stacks 0BKS "basiswise acyclicity condition"]
#check @BasiswiseAcyclic
@[stacks 0BKS "basiswise R¹-limit vanishing condition"]
#check @BasiswiseR1Vanishing
@[stacks 0BKS "basiswise acyclicity equivalence"]
#check @basiswiseAcyclic_iff
@[stacks 0BKS "basiswise R¹-limit vanishing equivalence"]
#check @basiswiseR1Vanishing_iff
@[stacks 0BKS "derived-limit cohomology comparison"]
#check @Comparison.isoLimit
@[stacks 0BKS "derived-limit presentation existence"]
#check @existsDerivedLimit

end
