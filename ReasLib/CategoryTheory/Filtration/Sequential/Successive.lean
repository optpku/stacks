/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.Filtration.Sequential

/-!
# Sequential filtrations with controlled successive pieces

This file refines a sequential colimit presentation by recording short exact rows for the
successive pieces.  Both the allowed step maps and the property of the pieces remain parameters.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A sequential filtration of `P` presents it as the colimit of stages starting at zero.  Each
successive stage fits into a specified short exact row whose first map belongs to `stepProperty`
and whose quotient satisfies `pieceProperty`. -/
structure SequentialFiltration (P : C) (stepProperty : MorphismProperty C)
    (pieceProperty : ObjectProperty C) extends SequentialColimitFiltration P where
  /-- The initial filtration stage is zero. -/
  stageZero : IsZero (stage 0)
  /-- The successive pieces. -/
  piece : ℕ → C
  /-- The quotient map from a successor stage to its successive piece. -/
  projection : ∀ n : ℕ, stage (n + 1) ⟶ piece n
  /-- A filtration step followed by its quotient map is zero. -/
  zero_comp : ∀ n : ℕ, step n ≫ projection n = 0
  /-- Every successive filtration row is short exact. -/
  shortExact : ∀ n : ℕ,
    (ShortComplex.mk (step n) (projection n) (zero_comp n)).ShortExact
  /-- Every filtration step belongs to the designated morphism property. -/
  step_mem : ∀ n : ℕ, stepProperty (step n)
  /-- Every successive piece satisfies the designated object property. -/
  piece_mem : ∀ n : ℕ, pieceProperty (piece n)

namespace SequentialFiltration

/-- The stage diagram underlying a sequential filtration. -/
abbrev diagram {P : C} {stepProperty : MorphismProperty C}
    {pieceProperty : ObjectProperty C}
    (F : SequentialFiltration P stepProperty pieceProperty) : ℕ ⥤ C :=
  F.toSequentialColimitFiltration.diagram

/-- The chosen colimit cocone underlying a sequential filtration. -/
abbrev cocone {P : C} {stepProperty : MorphismProperty C}
    {pieceProperty : ObjectProperty C}
    (F : SequentialFiltration P stepProperty pieceProperty) : Cocone F.diagram :=
  F.toSequentialColimitFiltration.cocone

/-- The short complex defining the `n`th successive piece. -/
abbrev pieceShortComplex {P : C} {stepProperty : MorphismProperty C}
    {pieceProperty : ObjectProperty C}
    (F : SequentialFiltration P stepProperty pieceProperty) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (F.step n) (F.projection n) (F.zero_comp n)

/-- A sequential filtration supplies the colimit of its stage diagram. -/
instance instHasColimit {P : C} {stepProperty : MorphismProperty C}
    {pieceProperty : ObjectProperty C}
    (F : SequentialFiltration P stepProperty pieceProperty) : HasColimit F.diagram :=
  F.toSequentialColimitFiltration.instHasColimit

/-- The canonical comparison from the colimit of the stages to the filtered object. -/
noncomputable abbrev colimitComparison {P : C} {stepProperty : MorphismProperty C}
    {pieceProperty : ObjectProperty C}
    (F : SequentialFiltration P stepProperty pieceProperty) : colimit F.diagram ≅ P :=
  F.toSequentialColimitFiltration.colimitComparison

end SequentialFiltration

end CategoryTheory
