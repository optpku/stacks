/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.LocalCriterion.ValuationRing
import StacksCheckRecall

@[expose] public section

universe u v w x

namespace LinearMap

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [IsLocalRing B]
variable [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
variable {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N]
variable [Module A N] [IsScalarTower A B N]
variable {M : Type x} [AddCommGroup M] [Module B M] [Module.Finite B M]
variable [Module A M] [IsScalarTower A B M] [Module.Flat A M]

/- Lemma 37.18.1 (1): for a finite map of modules over a local essentially finite-type
algebra over a valuation ring, injectivity on the closed-fiber quotient implies injectivity. -/
@[stacks 0GSG]
#check (LinearMap.injective_of_finite_essFiniteTypeLocalValuationRing :
  ∀ (u : N →ₗ[B] M),
    Function.Injective
      ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A)) →
      Function.Injective u)

/- Lemma 37.18.1 (2): under the same hypotheses, the quotient of the target by the range of
the map is flat over the valuation ring. -/
@[stacks 0GSG]
#check (LinearMap.flat_quotient_range_of_finite_essFiniteTypeLocalValuationRing :
  ∀ (u : N →ₗ[B] M),
    Function.Injective
      ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A)) →
      Module.Flat A (M ⧸ LinearMap.range u))

end

end LinearMap
