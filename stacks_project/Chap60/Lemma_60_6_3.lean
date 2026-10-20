module

public import stacks_project.Chap60.Remark_60_6_7_Forms
public import ReasLib.RingTheory.DividedPowers.Category.Conormal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 60.6.3 (1): for a self-pushout of divided-power rings, the fold-kernel
intersection with the distinguished ideal is stable under divided powers. -/
@[stacks 07HT] #check
  (DividedPowerRing.Pushout.isSubDPIdeal_kernel :
    ∀ {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
      (hpush : IsPushout f f s₀ s₁),
      DividedPowers.IsSubDPIdeal B₁.dividedPowers
        (RingHom.ker (DividedPowerRing.Pushout.fold f s₀ s₁ hpush).toRingHom ⊓ B₁.ideal))

/- Lemma 60.6.3 (2): the canonical comparison from divided-power differentials
to the fold-kernel quotient is bijective. -/
@[stacks 07HT] #check
  (DividedPowerRing.Pushout.kernelComparison_bijective :
    ∀ {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
      (hpush : IsPushout f f s₀ s₁),
      Function.Bijective (DividedPowerRing.Pushout.kernelComparison f s₀ s₁ hpush))

end
