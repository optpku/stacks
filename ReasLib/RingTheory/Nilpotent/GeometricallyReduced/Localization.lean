/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of Geometrically Reduced Algebras

This leaf owns the localization closure of `Algebra.IsGeometricallyReduced`.
The primary theorem is stated for an arbitrary localization algebra, since
downstream constructions often use a chosen localization model rather than
`Localization M` itself.  The standard localization receives the corresponding
canonical instance as a specialization.
-/

@[expose] public section

universe u v w

namespace Algebra.IsGeometricallyReduced

/-- An arbitrary localization of a geometrically reduced algebra is
geometrically reduced over the same commutative base ring. -/
@[stacks 030T]
theorem of_isLocalization
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B]
    [Algebra.IsGeometricallyReduced R A] :
    Algebra.IsGeometricallyReduced R B := sorry

/-- Explicit-hypothesis form of `of_isLocalization`; use this bridge when geometric reducedness
of the source algebra is proposition-valued data rather than an installed instance. -/
@[stacks 030T "explicit localization bridge"]
theorem of_isLocalization_of
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B]
    (hA : Algebra.IsGeometricallyReduced R A) :
    Algebra.IsGeometricallyReduced R B := sorry

end Algebra.IsGeometricallyReduced

namespace Localization

/-- The canonical localization of a geometrically reduced algebra is
geometrically reduced. -/
@[stacks 030T "geometrically reduced localization instance"]
instance instIsGeometricallyReduced
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid A) [Algebra.IsGeometricallyReduced R A] :
    Algebra.IsGeometricallyReduced R (Localization M) := sorry

end Localization
