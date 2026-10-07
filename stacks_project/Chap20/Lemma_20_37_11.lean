module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology

/- Lemma 20.37.11 (0BKU): let `(X, 𝒪_X)` be a ringed space, let `(K_n)` be an inverse system in
`D(𝒪_X)`, and let `K = R lim_n K_n` be a chosen derived limit. Assume every open subset of `X`
admits a covering by members of `ℬ`, that for every `U ∈ ℬ`, every `n`, and every `p > 0` one
has `IsZero ((𝓗[q](X, K_n)).H' p U)`, and that for every `U ∈ ℬ` the inverse system
`n ↦ (𝓗[q](X, K_n)).H' 0 U` has vanishing `R^1 lim`. Then the cohomology sheaf `𝓗[q](X, K)` is
isomorphic to the inverse limit sheaf `limit (Ksys ⋙ H^q ⋙ moduleUnderlyingSheaf X)`. -/
@[stacks 0BKU "basiswise derived-limit cohomology comparison"]
#check @Comparison.isoLimitOfSheaves

@[stacks 0BKU "cohomology sheaf tower"]
#check @cohomologySheafTower
@[stacks 0BKU "section cohomology tower"]
#check @sectionCohomologyTower
@[stacks 0BKU "basiswise acyclicity for the limit comparison"]
#check @BasiswiseAcyclic
@[stacks 0BKU "sheafwise acyclicity for the limit comparison"]
#check @SheafwiseAcyclic
@[stacks 0BKU "basiswise and sheafwise acyclicity equivalence"]
#check @basiswiseAcyclic_iff_sheafwiseAcyclic
@[stacks 0BKU "derived-limit cohomology comparison"]
#check @Comparison.isoLimit

end
