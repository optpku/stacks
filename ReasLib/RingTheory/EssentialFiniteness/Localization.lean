module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.EssentialFiniteness.BaseChange

/-!
# Essential Finite Presentation After Source Localization

This leaf owns the change-of-base result for an essentially finitely presented
algebra when its source ring is localized.
-/

@[expose] public section

universe u v w

namespace Algebra.EssFinitePresentation

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Essential finite presentation is preserved when the source algebra is a
localization of the original source ring. -/
theorem of_sourceLocalization
    (N : Submonoid R) [IsLocalization N S]
    (h : Algebra.EssFinitePresentation R T) :
    Algebra.EssFinitePresentation S T := sorry

end Algebra.EssFinitePresentation
