/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Preadditive.Injective.Split

@[expose] public section

/-!
# Admissible Morphisms and Short Exact Sequences

This module defines admissibility relative to a functor which forgets structure: an admissible
monomorphism or epimorphism becomes split after applying that functor.  It also packages the
corresponding notion for short exact sequences.
-/

open CategoryTheory

universe u v w x

section

variable {C : Type u} [Category.{v} C]
variable {Graded : Type w} [Category.{x} Graded]

/-- A morphism is an admissible monomorphism relative to `forgetToGraded` when its image is split
monic. -/
@[stacks 09JT]
abbrev IsAdmissibleMono (forgetToGraded : C ⥤ Graded) {K L : C} (ι : K ⟶ L) : Prop :=
  IsSplitMono (forgetToGraded.map ι)

/-- An admissible monomorphism is equivalently a morphism whose image under `forgetToGraded` has
a retraction. -/
theorem isAdmissibleMono_iff_exists_retraction
    (forgetToGraded : C ⥤ Graded) {K L : C} (ι : K ⟶ L) :
    IsAdmissibleMono forgetToGraded ι ↔
      ∃ retraction : forgetToGraded.obj L ⟶ forgetToGraded.obj K,
        forgetToGraded.map ι ≫ retraction = 𝟙 (forgetToGraded.obj K) := sorry

/-- A morphism is admissibly monic whenever its forgotten source is injective and its forgotten
map is monic. -/
@[stacks 09K2 "injective source criterion for admissible monomorphisms"]
theorem isAdmissibleMono_of_mono_of_injective
    (forgetToGraded : C ⥤ Graded) {K L : C} (ι : K ⟶ L)
    [Mono (forgetToGraded.map ι)] [Injective (forgetToGraded.obj K)] :
    IsAdmissibleMono forgetToGraded ι := sorry

/-- A morphism is an admissible epimorphism relative to `forgetToGraded` when its image is split
epic. -/
@[stacks 09JT]
abbrev IsAdmissibleEpi (forgetToGraded : C ⥤ Graded) {L M : C} (π : L ⟶ M) : Prop :=
  IsSplitEpi (forgetToGraded.map π)

/-- An admissible epimorphism is equivalently a morphism whose image under `forgetToGraded` has
a section. -/
theorem isAdmissibleEpi_iff_exists_section
    (forgetToGraded : C ⥤ Graded) {L M : C} (π : L ⟶ M) :
    IsAdmissibleEpi forgetToGraded π ↔
      ∃ gradedSection : forgetToGraded.obj M ⟶ forgetToGraded.obj L,
        gradedSection ≫ forgetToGraded.map π = 𝟙 (forgetToGraded.obj M) := sorry

/-- A morphism is admissibly epic whenever its forgotten target is projective and its forgotten
map is epic. -/
theorem isAdmissibleEpi_of_epi_of_projective
    (forgetToGraded : C ⥤ Graded) {L M : C} (π : L ⟶ M)
    [Epi (forgetToGraded.map π)] [Projective (forgetToGraded.obj M)] :
    IsAdmissibleEpi forgetToGraded π := sorry

end

section

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {Graded : Type w} [Category.{x} Graded]

/-- A short exact sequence is admissible relative to `forgetToGraded` when both of its maps are
admissible after forgetting structure. -/
@[stacks 09JT]
class IsAdmissibleShortExact (forgetToGraded : C ⥤ Graded) (S : ShortComplex C) : Prop where
  /-- The sequence is short exact before forgetting structure. -/
  shortExact : S.ShortExact
  /-- Its first map becomes split monic after forgetting structure. -/
  isAdmissibleMono : IsAdmissibleMono forgetToGraded S.f
  /-- Its second map becomes split epic after forgetting structure. -/
  isAdmissibleEpi : IsAdmissibleEpi forgetToGraded S.g

attribute [instance] IsAdmissibleShortExact.isAdmissibleMono
attribute [instance] IsAdmissibleShortExact.isAdmissibleEpi

/-- An admissible short exact sequence is exactly a short exact sequence with admissible first
and second maps. -/
theorem isAdmissibleShortExact_iff
    (forgetToGraded : C ⥤ Graded) (S : ShortComplex C) :
    IsAdmissibleShortExact forgetToGraded S ↔
      S.ShortExact ∧
        IsAdmissibleMono forgetToGraded S.f ∧
        IsAdmissibleEpi forgetToGraded S.g := sorry

/-- An admissible short exact sequence is equivalently a short exact sequence whose forgotten
maps admit explicit retraction and section data. -/
theorem isAdmissibleShortExact_iff_exists_retraction_section
    (forgetToGraded : C ⥤ Graded) (S : ShortComplex C) :
    IsAdmissibleShortExact forgetToGraded S ↔
      S.ShortExact ∧
        (∃ retraction : forgetToGraded.obj S.X₂ ⟶ forgetToGraded.obj S.X₁,
          forgetToGraded.map S.f ≫ retraction = 𝟙 (forgetToGraded.obj S.X₁)) ∧
        (∃ gradedSection : forgetToGraded.obj S.X₃ ⟶ forgetToGraded.obj S.X₂,
          gradedSection ≫ forgetToGraded.map S.g = 𝟙 (forgetToGraded.obj S.X₃)) := sorry

end
