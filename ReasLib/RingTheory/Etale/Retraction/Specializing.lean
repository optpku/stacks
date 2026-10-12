/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Retraction
public import ReasLib.RingTheory.Localization.Specializing

@[expose] public section

universe u

namespace Algebra.HasFaithfullyFlatEtaleRetraction

/-- The faithfully flat étale retraction property passes to specializing
localizations at the unit element. -/
instance specializing {A : Type u} [CommRing A]
    [HasFaithfullyFlatEtaleRetraction A] (I : Ideal A) :
    HasFaithfullyFlatEtaleRetraction (Localization.specializing (1 : A) I) := sorry

end Algebra.HasFaithfullyFlatEtaleRetraction
