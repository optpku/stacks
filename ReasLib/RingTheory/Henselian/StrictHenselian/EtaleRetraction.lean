module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.Etale.Retraction
public import ReasLib.RingTheory.Henselian.StrictHenselian

@[expose] public section

universe u

namespace Algebra.HasFaithfullyFlatEtaleRetraction

/-- If every faithfully flat étale ring map out of a commutative ring has a retraction,
then its localization at any maximal ideal is strictly henselian. -/
instance strictlyHenselian_atMaximalIdeal
    {A : Type u} [CommRing A] [HasFaithfullyFlatEtaleRetraction A]
    (m : Ideal A) [m.IsMaximal] :
    StrictHenselianLocalRing (Localization.AtPrime m) := sorry

end Algebra.HasFaithfullyFlatEtaleRetraction
