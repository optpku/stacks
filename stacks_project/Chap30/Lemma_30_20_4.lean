module

public import stacks_project.Chap30.Lemma_30_20_4_Quotient
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 30.20.4 (1): let `A` be a Noetherian ring, `I ⊂ A` an ideal, `f : X ⟶ Spec A`
proper, and `F` coherent on `X`. Then for every `p` there is some `c` such that
`Ker(H^p(X, F) ⟶ H^p(X, F / I^n F)) ≤ I^(n-c) H^p(X, F)` for all `n ≥ c`. -/
@[stacks 02OB] #check Hom.IdealPowerCohomology.Quotient.ker_le

/- Lemma 30.20.4 (2): under the same hypotheses, the inverse system
`n ↦ H^p(X, F / I^n F)` satisfies the Mittag-Leffler condition. -/
@[stacks 02OB] #check Hom.IdealPowerCohomology.Quotient.isMittagLeffler

/- Lemma 30.20.4 (3): under the same hypotheses, some `c` makes
`Im(H^p(F / I^k F) ⟶ H^p(F / I^n F)) = Im(H^p(F) ⟶ H^p(F / I^n F))`
for all `k ≥ n + c`. -/
@[stacks 02OB] #check Hom.IdealPowerCohomology.Quotient.image_eq

#check @Hom.IdealPowerCohomology.Quotient.existsStabilization
#check @Hom.IdealPowerCohomology.Quotient.tower
