/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.EssentialFiniteness.RingHom

/-!
# Essentially etale algebras and ring homomorphisms

This module owns the canonical essentially-etale predicates.  As for
`Algebra.EssSmooth`, the primary algebra predicate is intrinsic: formal
etaleness together with essential finite presentation.  The localization of
an etale algebra is exposed as an equivalent presentation, not as the root
representation.
@stack 0GS6
-/

@[expose] public section

universe u v w

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra is essentially etale when it is formally etale and
essentially of finite presentation over `R`. -/
@[stacks 0GS6 "essentially etale algebra predicate"]
class EssEtale : Prop where
  /-- An essentially etale algebra is formally etale. -/
  formallyEtale : FormallyEtale R S
  /-- An essentially etale algebra is essentially of finite presentation. -/
  essFinitePresentation : EssFinitePresentation R S

/-- Characterize essential etaleness by its two intrinsic properties. -/
theorem essEtale_iff_formallyEtale_and_essFinitePresentation :
    EssEtale R S ↔ FormallyEtale R S ∧ EssFinitePresentation R S := sorry

/-- Characterize an essentially etale algebra as a localization of an etale
algebra.  This is the presentation used by local structure theorems. -/
theorem essEtale_iff_exists_etale :
    EssEtale R S ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (M : Submonoid P), Etale R P ∧ IsLocalization M S := sorry

/-- A localization of an etale `R`-algebra is essentially etale over `R`. -/
theorem EssEtale.of_isLocalization
    (P : Type w) [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Etale R P] (M : Submonoid P) [IsLocalization M S] :
    EssEtale R S := sorry

/-- An etale algebra is essentially etale. -/
instance EssEtale.of_etale [Etale R S] : EssEtale R S := sorry

/-- An essentially etale algebra is flat over its base. -/
theorem EssEtale.flat [EssEtale R S] : Module.Flat R S := sorry

attribute [instance]
  EssEtale.formallyEtale EssEtale.essFinitePresentation EssEtale.flat

end Algebra

namespace RingHom

/-- The map-first essentially-etale predicate, formed with the algebra
structure induced by the ring homomorphism. -/
@[algebraize RingHom.EssEtale.toAlgebra,
  stacks 0GS6 "essentially etale ring-map predicate"]
def EssEtale {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  @Algebra.EssEtale R S _ _ f.toAlgebra

/-- The map-first predicate agrees with the algebra predicate on an ambient
algebra map. -/
theorem essEtale_algebraMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).EssEtale ↔ Algebra.EssEtale R S := sorry

/-- A ring homomorphism is essentially etale exactly when it is formally
etale and essentially of finite presentation. -/
theorem essEtale_def
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    f.EssEtale ↔ f.FormallyEtale ∧ f.EssFinitePresentation := sorry

/-- A ring homomorphism is essentially etale exactly when it factors as an
etale map followed by a localization map. -/
theorem essEtale_iff_exists_etale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    f.EssEtale ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (g : R →+* P),
        g.Etale ∧ ∃ (M : Submonoid P) (h : P →+* S),
          M.IsLocalizationMap h ∧ f = h.comp g := sorry

namespace EssEtale

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-- The algebra induced by an essentially etale map is essentially etale. -/
theorem toAlgebra {f : R →+* S} (hf : f.EssEtale) :
    @Algebra.EssEtale R S _ _ f.toAlgebra := sorry

/-- An etale ring homomorphism is essentially etale. -/
theorem of_etale {f : R →+* S} (hf : f.Etale) : f.EssEtale := sorry

/-- A localization ring homomorphism is essentially etale. -/
theorem of_isLocalization (f : R →+* S) (M : Submonoid R)
    (hf : M.IsLocalizationMap f) : f.EssEtale := sorry

/-- An essentially etale ring homomorphism is formally etale. -/
theorem formallyEtale {f : R →+* S} (hf : f.EssEtale) : f.FormallyEtale := sorry

/-- An essentially etale ring homomorphism is essentially of finite
presentation. -/
theorem essFinitePresentation {f : R →+* S} (hf : f.EssEtale) :
    f.EssFinitePresentation := sorry

/-- An essentially etale ring homomorphism is flat. -/
theorem flat {f : R →+* S} (hf : f.EssEtale) : f.Flat := sorry

/-- Composition of essentially etale ring homomorphisms is essentially
etale. -/
theorem comp {f : R →+* S} {g : S →+* T} (hf : f.EssEtale) (hg : g.EssEtale) :
    (g.comp f).EssEtale := sorry

/-- Localization-away maps are essentially etale. -/
theorem holdsForLocalizationAway :
    RingHom.HoldsForLocalizationAway RingHom.EssEtale := sorry

/-- The identity ring homomorphism is essentially etale. -/
theorem id (R : Type u) [CommRing R] : (RingHom.id R).EssEtale := sorry

/-- Essential etaleness is stable under composition. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition RingHom.EssEtale := sorry

/-- Essential etaleness is stable under base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.EssEtale := sorry

/-- Essential etaleness is invariant under isomorphisms of ring maps. -/
theorem respectsIso : RingHom.RespectsIso RingHom.EssEtale := sorry

end EssEtale

end RingHom
