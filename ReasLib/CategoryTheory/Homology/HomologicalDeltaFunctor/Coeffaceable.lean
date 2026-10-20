/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor
public import ReasLib.CategoryTheory.ObjectProperty.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coeffaceable Functors and Universal Homological Delta Functors

This leaf is the lower-indexed companion of the cohomological effaceability API.  It isolates the
epi-cover criterion used to prove universality from any particular derived or sheaf model.
-/

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory

open Limits

namespace Functor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]

/-- A functor is coeffaceable when every target object admits an epimorphism on which the functor
acts by the zero morphism. -/
def IsCoeffaceable (F : A ⥤ B) : Prop :=
  ∀ X : A, ∃ (Y : A) (p : Y ⟶ X), Epi p ∧ F.map p = 0

namespace IsCoeffaceable

/-- A functor is coeffaceable if it vanishes on an object property from which every object admits
an epimorphic cover. -/
theorem of_vanishesOn {F : A ⥤ B} {P : ObjectProperty A} [P.HasEpiCover]
    (hP : ∀ ⦃Y : A⦄, P Y → IsZero (F.obj Y)) :
    F.IsCoeffaceable := sorry

/-- Naturally isomorphic functors are simultaneously coeffaceable. -/
theorem iff_of_iso {F G : A ⥤ B} (e : F ≅ G) :
    F.IsCoeffaceable ↔ G.IsCoeffaceable := sorry

end IsCoeffaceable

end Functor

namespace HomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- Degree-zero maps into a homological delta functor extend uniquely when every positive
degree is coeffaceable. -/
@[stacks 010T "universal homological delta functor from coeffaceability"]
theorem isUniversal_of_coeffaceable (F : HomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → (F n).obj.IsCoeffaceable) :
    F.IsUniversal := sorry

end HomologicalDeltaFunctor

end CategoryTheory
