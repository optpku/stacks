module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.FlatBaseChange

/-!
# Cotangent invariance under source localization

This leaf records the source-localization specialization of first cotangent
homology invariance.  The corresponding Kähler-differential API belongs to
`ReasLib.RingTheory.Kaehler.Unramified`.
-/

@[expose] public section

universe u v w

namespace Algebra.H1Cotangent

variable {A : Type u} {Aₛ : Type v} {B : Type w}
variable [CommRing A] [CommRing Aₛ] [CommRing B]
variable [Algebra A B]

/-- Lemma 10.134.11, tag `07BS`: localizing the source algebra induces a
bijective canonical map on first cotangent homology. -/
@[stacks 07BS]
theorem map_bijective_of_isLocalization_source
    (S : Submonoid A) [Algebra A Aₛ] [IsLocalization S Aₛ] [Algebra Aₛ B]
    [IsScalarTower A Aₛ B] :
    Function.Bijective (map A Aₛ B B) := sorry

end Algebra.H1Cotangent
