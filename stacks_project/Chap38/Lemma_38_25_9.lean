module

public import ReasLib.Algebra.Module.PureSpreadout.Fiberwise
import StacksCheckRecall

@[expose] public section

universe u v w x z

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (S : Submonoid B) {N : Type w} [AddCommGroup N]
variable [Module (Localization S) N] [Module B N] [Module A N]
variable [IsScalarTower B (Localization S) N] [IsScalarTower A B N]
variable [Module.FinitePresentation (Localization S) N]
variable {M : Type x} [AddCommGroup M] [Module A M]

/- Lemma 38.25.9: in the setup of 38.25.6.1, if `N` and `M` are flat over
`A` and an `A`-linear map `u : N →ₗ[A] M` is injective on every residue-field
fiber, then `u` is universally injective over `A`. -/
@[stacks 0AT9] #check
  (LinearMap.universallyInjective_of_fiberInjective (S := S) :
    (algebraMap A B).FinitePresentation →
      ∀ [Module.Flat A N] [Module.Flat A M] (u : N →ₗ[A] M),
        (∀ p : PrimeSpectrum A, u.IsFiberInjectiveAt p) →
          LinearMap.UniversallyInjective.{u, w, x, max u v w x z} u)
