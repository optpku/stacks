module

public import ReasLib.RingTheory.DividedPowers.Category.Conormal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open DividedPowers

/- Lemma 60.6.5 (1): the fold-kernel intersection with the distinguished ideal is preserved by
the divided-power structure. -/
@[stacks 07HV] #check (DividedPowerRing.Pushout.isSubDPIdeal_kernel :
  ∀ {A B B₁ : DividedPowerRing.{_}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁),
    DividedPowers.IsSubDPIdeal B₁.dividedPowers
      (RingHom.ker (DividedPowerRing.Pushout.fold f s₀ s₁ hpush).toRingHom ⊓ B₁.ideal))

/- Lemma 60.6.5 (2): the relative divided-power differential is canonically equivalent to the
fold-kernel quotient by the ordinary square and the second-order divided-power ideal. -/
@[stacks 07HV] #check (DividedPowerRing.Pushout.kernelComparisonEquiv :
  ∀ {A B B₁ : DividedPowerRing.{_}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁),
    KaehlerDifferential.DeRham.dividedPowerDifferential f.toRingHom B.dividedPowers ≃ₗ[B]
      DividedPowerRing.Pushout.kernelQuotient f s₀ s₁ hpush)

#check (DividedPowerRing.Pushout.kernelComparisonEquiv_apply :
  ∀ {A B B₁ : DividedPowerRing.{_}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (b : B),
    DividedPowerRing.Pushout.kernelComparisonEquiv f s₀ s₁ hpush
        (KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation
          f.toRingHom B.dividedPowers b) =
      DividedPowerRing.Pushout.kernelDifference f s₀ s₁ hpush b)
