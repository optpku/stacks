/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.RingTheory.Algebra.IsEpi.TensorSquare
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars along algebra epimorphisms

@stack 08YS

An algebra epimorphism is exactly a map for which restriction of scalars on module categories is
fully faithful.  The public criterion keeps `Nonempty FullyFaithful` as the source-facing
proposition, while the `Full` instance is exposed separately so ordinary typeclass-driven module
arguments do not need local instance reconstruction.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Algebra.IsEpi

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An epic algebra makes restriction of scalars full on module categories. -/
@[stacks 08YS "restriction full"]
instance full_of_isEpi [Algebra.IsEpi R S] :
    (ModuleCat.restrictScalars.{w} (algebraMap R S)).Full := sorry

/-- Explicit-hypothesis form of `full_of_isEpi`. This avoids installing a
local typeclass when epimorphy is obtained from ordinary theorem data. -/
@[stacks 08YS "explicit restriction full"]
theorem restrictScalars_full (h : Algebra.IsEpi R S) :
    (ModuleCat.restrictScalars.{w} (algebraMap R S)).Full :=
  @full_of_isEpi R S _ _ _ h

/-- Algebra epimorphy is equivalent to full faithfulness of restriction of scalars. -/
@[stacks 08YS "algebra form"]
theorem iff_restrictScalars_fullyFaithful :
    Algebra.IsEpi R S ↔
      Nonempty ((ModuleCat.restrictScalars.{w} (algebraMap R S)).FullyFaithful) := sorry

end Algebra.IsEpi

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A commutative-ring epimorphism is exactly a ring map whose restriction-of-scalars functor on
module categories is fully faithful. -/
@[stacks 08YS]
theorem epi_iff_restrictScalars_fullyFaithful (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔
      Nonempty ((ModuleCat.restrictScalars.{w} f).FullyFaithful) := sorry

/-- An epimorphic commutative-ring map makes restriction of scalars full. -/
@[stacks 08YS "ring-hom restriction full"]
instance full_of_epi (f : R →+* S) [Epi (CommRingCat.ofHom f)] :
    (ModuleCat.restrictScalars.{w} f).Full := sorry

end RingHom
