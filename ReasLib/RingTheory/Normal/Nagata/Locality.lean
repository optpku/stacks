/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalProperty
public import ReasLib.RingTheory.Normal.Nagata.Characterization
public import ReasLib.RingTheory.Normal.Nagata.EssentialFiniteness

@[expose] public section

/-!
# Principal-Open Locality of Japanese Conditions

This leaf records finite principal-open cover criteria for the universally
Japanese and Nagata conditions.
-/

universe u

namespace UniversallyJapaneseRing

/-- The universally Japanese property of commutative rings is invariant under
isomorphisms. -/
@[instance]
theorem isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ UniversallyJapaneseRing.{u, u} A) := sorry

/-- A finite principal-open cover by universally Japanese localizations makes
the base ring universally Japanese. -/
@[stacks 032V "(1)"]
theorem of_localizationAway {R : Type u} [CommRing R]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, UniversallyJapaneseRing (Localization.Away f.1)) :
    UniversallyJapaneseRing R := sorry

/-- Being universally Japanese is a local property of commutative rings. -/
@[instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal
      (fun A : CommRingCat.{u} ↦ UniversallyJapaneseRing.{u, u} A) := sorry

end UniversallyJapaneseRing

namespace NagataRing

/-- The Nagata property of commutative rings is invariant under isomorphisms. -/
@[instance]
theorem isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ NagataRing A) := sorry

/-- A finite principal-open cover by Nagata localizations makes the base ring
Nagata. -/
@[stacks 032V "(2)"]
theorem of_localizationAway {R : Type u} [CommRing R]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, NagataRing (Localization.Away f.1)) :
    NagataRing R := sorry

/-- Being Nagata is a local property of commutative rings. -/
@[instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ NagataRing A) := sorry

end NagataRing
