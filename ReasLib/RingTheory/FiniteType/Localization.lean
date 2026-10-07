module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace Algebra.FiniteType

/-- If a finite-type algebra map is surjective after localization at a submonoid,
then it is surjective after localization away from some element of that submonoid. -/
theorem exists_awayMap_surjective {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (S : Submonoid A)
    (h_surj : Function.Surjective
      (algebraMap (Localization S) (Localization (Algebra.algebraMapSubmonoid B S)))) :
    ∃ f : S, Function.Surjective (Localization.awayMap (algebraMap A B) (f : A)) := sorry

end Algebra.FiniteType
