/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Sequential modules over a varying ring system

@stack 091D

This file owns the module category attached to a sequential inverse system of commutative
rings.  The ring system itself is modeled canonically as a functor
`ℕᵒᵖ ⥤ CommRingCat`; the bottom-topology sheaf presentation is definitionally the same
stagewise ring system, so evaluation and successor transition maps require no transport casts.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem

/-! ### Ring systems -/

/-- A family of commutative rings and successor maps as a sequential inverse system. -/
@[stacks 091D "sequential inverse system of commutative rings"]
abbrev sequentialRingSystem
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    SequentialInverseSystem CommRingCat.{u} :=
  @Functor.ofOpSequence CommRingCat.{u} _
    (fun n ↦ CommRingCat.of (A n))
    (fun n ↦ CommRingCat.ofHom (ρ n))

/-- The underlying `RingCat`-valued functor of a commutative-ring system. -/
@[stacks 091D "underlying ring-category system"]
abbrev ringSystemAsRingCat (F : SequentialInverseSystem CommRingCat.{u}) :
    SequentialInverseSystem RingCat.{u} :=
  F ⋙ forget₂ CommRingCat RingCat

/-- The canonical bottom-topology sheaf of rings associated to `F`. -/
@[stacks 091D "bottom-topology ring sheaf of a sequential system"]
abbrev bottomRingSheaf (F : SequentialInverseSystem CommRingCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology ℕ) RingCat.{u} :=
  ⟨ringSystemAsRingCat F, Presheaf.isSheaf_bot _⟩

/-- The `RingCat` system associated to a family `A` and successor maps `ρ`. -/
@[stacks 091D "RingCat presentation of a sequential ring system"]
abbrev sequentialRingSystemAsRingCat
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    SequentialInverseSystem RingCat.{u} :=
  ringSystemAsRingCat (sequentialRingSystem A ρ)

/-- The bottom-topology ring sheaf associated to a family `A` and successor maps `ρ`. -/
@[stacks 091D "bottom ring sheaf of a sequential ring system"]
abbrev sequentialRingSystemRingSheaf
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :
    Sheaf (⊥ : GrothendieckTopology ℕ) RingCat.{u} :=
  bottomRingSheaf (sequentialRingSystem A ρ)

/-- The successor map of `sequentialRingSystem A ρ` is the bundled map `ρ n`. -/
@[stacks 091D "successor map of a sequential ring system"]
theorem sequentialRingSystem_stepMap_eq
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    (sequentialRingSystem A ρ).stepMap n = CommRingCat.ofHom (ρ n) := sorry

/-! ### Varying-ring module categories -/

/-- The category of modules over the varying rings in `F`. -/
@[stacks 091D "modules over a sequential varying-ring system"]
abbrev ModuleSystem (F : SequentialInverseSystem CommRingCat.{u}) :=
  SheafOfModules.{v} (bottomRingSheaf F)

/-- Source-facing name for modules over the family `A` with successor maps `ρ`. -/
@[stacks 091D "source-facing sequential varying-ring module category"]
abbrev SeqRingMod
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) :=
  ModuleSystem (sequentialRingSystem A ρ)

/-- Evaluation of a varying-ring module system at its `n`th stage. -/
@[stacks 091D "stage evaluation for a sequential varying-ring module system"]
abbrev evaluation
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) :
    ModuleSystem.{u, v} F ⥤ ModuleCat.{v} ((ringSystemAsRingCat F).obj (op n)) :=
  SheafOfModules.evaluation (bottomRingSheaf F) (op n)

/-- Source-facing stage evaluation for a family `A` with successor maps `ρ`. -/
@[stacks 091D "source-facing stage evaluation"]
abbrev sequentialRingedModuleEvaluation
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    SeqRingMod.{u, v} A ρ ⥤ ModuleCat.{v} (A n) :=
  evaluation (sequentialRingSystem A ρ) n

/-- The successor transition from stage `n + 1` to stage `n`, with restriction of scalars. -/
@[stacks 091D "successor transition for a sequential varying-ring module system"]
abbrev evaluationStep
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) :
    evaluation F (n + 1) ⟶
      evaluation F n ⋙ ModuleCat.restrictScalars (F.stepMap n).hom :=
  Functor.whiskerLeft (SheafOfModules.forget (bottomRingSheaf F))
    (PresheafOfModules.restriction (ringSystemAsRingCat F)
      ((homOfLE (Nat.le_add_right n 1)).op))

/-- Source-facing successor transition for a family `A` with successor maps `ρ`. -/
@[stacks 091D "source-facing successor transition"]
abbrev sequentialRingedModuleEvaluationStep
    (A : ℕ → Type u) [∀ n, CommRing (A n)]
    (ρ : ∀ n, A (n + 1) →+* A n) (n : ℕ) :
    sequentialRingedModuleEvaluation.{u, v} A ρ (n + 1) ⟶
      sequentialRingedModuleEvaluation.{u, v} A ρ n ⋙
        ModuleCat.restrictScalars ((sequentialRingSystem A ρ).stepMap n).hom :=
  evaluationStep (sequentialRingSystem A ρ) n

/-- Stage evaluation is additive on morphisms. -/
@[stacks 091D "additivity of stage evaluation"]
instance evaluation_additive
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) :
    (evaluation.{u, v} F n).Additive where
  map_add := rfl

/-- Stage evaluation preserves zero morphisms. -/
@[stacks 091D "zero morphisms under stage evaluation"]
instance evaluation_preservesZeroMorphisms
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) :
    (evaluation.{u, v} F n).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

end CategoryTheory.SequentialInverseSystem

end
