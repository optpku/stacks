module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Essentially Finite-Type Japanese Algebras

This leaf records the essentially finite-type permanence properties of the
universally Japanese and Nagata conditions.
-/

universe u v

namespace UniversallyJapaneseRing

/-- An essentially finite-type algebra over a universally Japanese ring is
universally Japanese. -/
@[stacks 032S]
theorem of_essFiniteType {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [UniversallyJapaneseRing.{u, v} R] [Algebra.EssFiniteType R S] :
    UniversallyJapaneseRing.{v, v} S := sorry

end UniversallyJapaneseRing

namespace NagataRing

/-- A ring essentially of finite type over a Nagata ring is Nagata. -/
theorem of_essFiniteType {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [NagataRing R] [Algebra.EssFiniteType R S] : NagataRing S := sorry

/-- A localization of a Nagata ring is Nagata. -/
@[stacks 032U]
theorem of_isLocalization {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [NagataRing R] :
    NagataRing S := sorry

end NagataRing
