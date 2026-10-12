/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.EssentialFiniteness.RingHom

/-!
# Essentially smooth algebras

This leaf owns the localization-of-a-smooth-algebra formulation of essential
smoothness and its basic introduction interfaces.
-/

@[expose] public section

universe u v w

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The essentially smooth algebra predicate used in Lemma 23.10.1 (0FCW): formal smoothness
together with essential finite presentation.  The equivalent localization-of-a-smooth-algebra
presentation is exposed by `Algebra.essSmooth_iff_exists_smooth`. -/
@[stacks 0FCW "essentially smooth algebra predicate"]
class EssSmooth : Prop where
  /-- An essentially smooth algebra is formally smooth. -/
  formallySmooth : FormallySmooth R S
  /-- An essentially smooth algebra is essentially finitely presented. -/
  essFinitePresentation : EssFinitePresentation R S

/-- Essential smoothness is equivalent to formal smoothness and essential finite presentation. -/
theorem essSmooth_iff_formallySmooth_and_essFinitePresentation :
    EssSmooth R S ↔ FormallySmooth R S ∧ EssFinitePresentation R S := sorry

/-- The source-facing localization presentation of an essentially smooth algebra. -/
theorem essSmooth_iff_exists_smooth :
    EssSmooth R S ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (M : Submonoid P), Smooth R P ∧ IsLocalization M S := sorry

/-- A localization of a smooth `R`-algebra is essentially smooth over `R`. -/
theorem EssSmooth.of_isLocalization
    (P : Type w) [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Smooth R P] (M : Submonoid P) [IsLocalization M S] :
    EssSmooth R S := sorry

/-- A smooth `R`-algebra is essentially smooth over `R`. -/
theorem EssSmooth.of_smooth [Smooth R S] :
    EssSmooth R S := sorry

/-- Smooth `R`-algebras are essentially smooth over `R`. -/
instance of_smooth [Smooth R S] : EssSmooth R S := sorry

/-- A formally smooth, essentially finitely presented algebra is essentially smooth. -/
theorem EssSmooth.of_formallySmooth_of_essFinitePresentation
    (hformal : FormallySmooth R S) (hfinite : EssFinitePresentation R S) :
    EssSmooth R S := sorry

/-- An essentially smooth algebra is flat. -/
theorem EssSmooth.flat [EssSmooth R S] : Module.Flat R S := sorry

attribute [instance] EssSmooth.formallySmooth EssSmooth.essFinitePresentation EssSmooth.flat

end Algebra

namespace RingHom

/-- The map-first essentially smooth predicate used in Lemma 23.10.1 (0FCW), formed using the
algebra structure induced by the map itself. -/
@[algebraize RingHom.EssSmooth.toAlgebra,
  stacks 0FCW "essentially smooth ring-map predicate"]
def EssSmooth {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  @Algebra.EssSmooth R S _ _ f.toAlgebra

/-- The map-first essentially smooth predicate agrees with the algebra predicate on an ambient
algebra map. -/
theorem essSmooth_algebraMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).EssSmooth ↔ Algebra.EssSmooth R S := sorry

/-- A ring homomorphism is essentially smooth exactly when it is formally smooth and essentially
finitely presented. -/
@[stacks 0FCW "map-first definition of essential smoothness"]
theorem essSmooth_def
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    f.EssSmooth ↔ f.FormallySmooth ∧ f.EssFinitePresentation := sorry

/-- A ring homomorphism is essentially smooth exactly when it factors as a smooth map followed by
a localization map. -/
@[stacks 0FCW "map-first smooth-localization presentation"]
theorem essSmooth_iff_exists_smooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    f.EssSmooth ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (g : R →+* P),
        g.Smooth ∧ ∃ (M : Submonoid P) (h : P →+* S),
          M.IsLocalizationMap h ∧ f = h.comp g := sorry

namespace EssSmooth

variable {R : Type u} {S : Type v} {T : Type*}
variable [CommRing R] [CommRing S] [CommRing T]

/-- The algebra structure canonically induced by an essentially smooth ring map is essentially
smooth. -/
theorem toAlgebra {f : R →+* S} (hf : f.EssSmooth) :
    @Algebra.EssSmooth R S _ _ f.toAlgebra := sorry

/-- A smooth ring homomorphism is essentially smooth. -/
theorem of_smooth {f : R →+* S} (hf : f.Smooth) : f.EssSmooth := sorry

/-- A localization ring homomorphism is essentially smooth. -/
theorem of_isLocalization (f : R →+* S) (M : Submonoid R)
    (hf : M.IsLocalizationMap f) :
    f.EssSmooth := sorry

/-- An essentially smooth ring homomorphism is formally smooth. -/
theorem formallySmooth {f : R →+* S} (hf : f.EssSmooth) : f.FormallySmooth := sorry

/-- An essentially smooth ring homomorphism is essentially finitely presented. -/
theorem essFinitePresentation {f : R →+* S} (hf : f.EssSmooth) :
    f.EssFinitePresentation := sorry

/-- An essentially smooth ring homomorphism is flat. -/
theorem flat {f : R →+* S} (hf : f.EssSmooth) : f.Flat := sorry

/-- Composition of essentially smooth ring homomorphisms is essentially smooth. -/
theorem comp {f : R →+* S} {g : S →+* T} (hf : f.EssSmooth) (hg : g.EssSmooth) :
    (g.comp f).EssSmooth := sorry

/-- Localization-away maps are essentially smooth. -/
theorem holdsForLocalizationAway :
    RingHom.HoldsForLocalizationAway RingHom.EssSmooth := sorry

/-- The identity of a commutative ring is essentially smooth. -/
theorem id (R : Type u) [CommRing R] : (RingHom.id R).EssSmooth := sorry

/-- Essential smoothness is stable under composition of ring homomorphisms. -/
theorem stableUnderComposition : RingHom.StableUnderComposition RingHom.EssSmooth := sorry

/-- Essential smoothness is stable under base change. -/
theorem isStableUnderBaseChange : RingHom.IsStableUnderBaseChange RingHom.EssSmooth := sorry

/-- Essential smoothness is invariant under isomorphisms of ring maps. -/
theorem respectsIso : RingHom.RespectsIso RingHom.EssSmooth := sorry

end EssSmooth

end RingHom
