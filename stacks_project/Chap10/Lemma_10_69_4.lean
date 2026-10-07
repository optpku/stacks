module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Localization
public import ReasLib.RingTheory.Sequence.QuasiRegular.Localization
import StacksCheckRecall

@[expose] public section

/-! @stack 061Q -/

/-!
# Quasi-Regularity Near a Prime

The reusable localization infrastructure lives in ReasLib. This file records the source-facing
specialization to localization at a prime and localization away from one element.
-/

universe u v

open RingTheory

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.69.4, tag `061Q`: quasi-regularity at a prime spreads to a principal open
neighborhood of that prime. -/
@[stacks 061Q]
#check (Sequence.IsQuasiRegular.exists_away_of_atPrime (R := R) (M := M) :
  ∀ (p : Ideal R) [p.IsPrime] {rs : List R},
    Sequence.IsQuasiRegular (LocalizedModule.AtPrime p M)
        (rs.map (algebraMap R (Localization.AtPrime p))) →
      ∃ g : R, g ∉ p ∧
        Sequence.IsQuasiRegular (LocalizedModule.Away g M)
          (rs.map (algebraMap R (Localization.Away g))))

#check @Ideal.AssociatedGraded.localizedGradedModuleEquiv
#check @Sequence.IsQuasiRegular.localized_iff

end
