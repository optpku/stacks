module

public import stacks_project.Chap42.Situation_42_7_1
public import stacks_project.Chap42.Remark_42_35_5_Completion
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExteriorPower.ChernProduct
import Mathlib.Algebra.Ring.Subring.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

section

variable {S X : Scheme.{u}} (p : X ⟶ S)
variable [UniversallyCatenary S] [LocallyOfFiniteType p]
variable (δ : S → ℤ) [IsDimensionFunction δ]
variable (E : X.Modules) (r : ℕ) [E.IsFiniteLocallyFreeOfRank r] (hr : 0 < r)
variable (theory : Scheme.Modules.ExteriorPowerChernClassTheory X
  (Subring.center (ChowCohomology.Nonnegative.ring δ p)))

/- Lemma 42.55.1: for a positive-rank finite locally free module `E`, the alternating
product of the total Chern classes of `Λ[n] E` is `1` through degree `r - 1`, and its
degree-`r` term is `-((r - 1)! * c_r(E))`. Equality after `PowerSeries.trunc (r + 1)`
expresses the omitted terms of degree greater than `r`. -/
@[stacks 0FEE] #check
  (AlgebraicGeometry.Scheme.Modules.alternatingChernProduct_trunc theory E r hr :
    PowerSeries.trunc (r + 1)
        (AlgebraicGeometry.Scheme.Modules.alternatingChernProduct theory E r :
          PowerSeries (Subring.center (ChowCohomology.Nonnegative.ring δ p))) =
      1 - Polynomial.monomial r
        (((r - 1).factorial :
            Subring.center (ChowCohomology.Nonnegative.ring δ p)) *
          theory.topChern E r))

end
