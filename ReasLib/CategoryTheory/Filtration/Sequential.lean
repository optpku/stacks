/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Sequential
public import ReasLib.CategoryTheory.Limits.Countable
public import Mathlib.CategoryTheory.Limits.Presentation

@[expose] public section

/-!
# Sequential Colimit Filtrations

This leaf owns the categorical data of an increasing sequential filtration
whose supplied cocone exhibits a specified object as its colimit.  It is
independent of any condition on the successive quotients.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A sequential colimit filtration of `P` consists of stages, consecutive maps, and a chosen
cocone which exhibits `P` as their colimit. -/
structure SequentialColimitFiltration (P : C) where
  /-- The filtration stages. -/
  stage : ℕ → C
  /-- The consecutive filtration maps. -/
  step : ∀ n : ℕ, stage n ⟶ stage (n + 1)
  /-- The cocone maps from the stages to `P`. -/
  toCocone : Functor.ofSequence step ⟶ (Functor.const ℕ).obj P
  /-- The supplied cocone is colimiting. -/
  isColimit : IsColimit (Cocone.mk P toCocone)

namespace SequentialColimitFiltration

/-- The sequential diagram of stages of a sequential colimit filtration. -/
abbrev diagram {P : C} (F : SequentialColimitFiltration P) : ℕ ⥤ C :=
  Functor.ofSequence F.step

/-- The chosen colimit cocone of a sequential colimit filtration. -/
abbrev cocone {P : C} (F : SequentialColimitFiltration P) : Cocone F.diagram :=
  Cocone.mk P F.toCocone

/-- The map from the `n`th stage of a sequential colimit filtration to its colimit object. -/
abbrev coconeApp {P : C} (F : SequentialColimitFiltration P) (n : ℕ) : F.stage n ⟶ P :=
  F.toCocone.app n

/-- The stage maps of a sequential colimit filtration commute with its cocone maps. -/
@[reassoc]
theorem step_comp_coconeApp {P : C} (F : SequentialColimitFiltration P) (n : ℕ) :
    F.step n ≫ F.coconeApp (n + 1) = F.coconeApp n := sorry

/-- A sequential colimit filtration supplies the colimit of its stage diagram. -/
instance instHasColimit {P : C} (F : SequentialColimitFiltration P) : HasColimit F.diagram :=
  HasColimit.mk ⟨F.cocone, F.isColimit⟩

/-- The chosen colimit data supplied by a sequential colimit filtration. -/
abbrev hasColimit {P : C} (F : SequentialColimitFiltration P) : HasColimit F.diagram :=
  F.instHasColimit

/-- The canonical comparison from the chosen categorical colimit of the stage diagram to the
object presented by the filtration. -/
noncomputable def colimitComparison {P : C} (F : SequentialColimitFiltration P) :
    colimit F.diagram ≅ P :=
  (colimit.isColimit F.diagram).coconePointUniqueUpToIso F.isColimit

/-- The canonical colimit coprojection followed by the colimit comparison is the supplied stage
cocone map. -/
@[reassoc]
theorem colimit_ι_comp_colimitComparison_hom {P : C} (F : SequentialColimitFiltration P)
    (n : ℕ) :
    colimit.ι F.diagram n ≫ F.colimitComparison.hom = F.coconeApp n := sorry

/-- The supplied stage cocone map followed by the inverse colimit comparison is the canonical
colimit coprojection. -/
@[reassoc]
theorem coconeApp_comp_colimitComparison_inv {P : C} (F : SequentialColimitFiltration P)
    (n : ℕ) :
    F.coconeApp n ≫ F.colimitComparison.inv = colimit.ι F.diagram n := sorry

/-- Construct a sequential colimit filtration from a stage diagram with a selected colimit
comparison. -/
noncomputable def ofColimitIso {P : C} (stage : ℕ → C) (step : ∀ n, stage n ⟶ stage (n + 1))
    [HasColimit (Functor.ofSequence step)] (e : P ≅ colimit (Functor.ofSequence step)) :
    SequentialColimitFiltration P where
  stage := stage
  step := step
  toCocone :=
    ((ColimitPresentation.colimit (Functor.ofSequence step)).ofIso e.symm).ι
  isColimit :=
    ((ColimitPresentation.colimit (Functor.ofSequence step)).ofIso e.symm).isColimit

section

variable [Preadditive C] [HasCountableCoproducts C]

/-- The telescope relation of a sequential colimit filtration vanishes after the coproduct map
induced by its cocone. -/
theorem telescopeCompDescZero {P : C} (F : SequentialColimitFiltration P) :
    Limits.Sequential.telescopeMap F.diagram ≫ Limits.Sigma.desc F.toCocone.app = 0 := sorry

/-- The telescope short complex associated to a sequential colimit filtration. -/
noncomputable abbrev telescopeShortComplex {P : C} (F : SequentialColimitFiltration P) :
    ShortComplex C :=
  ShortComplex.mk (Limits.Sequential.telescopeMap F.diagram) (Limits.Sigma.desc F.toCocone.app)
    F.telescopeCompDescZero

end

section

variable [Abelian C] [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]

-- Local instance justification (instance diamond): the named sequential-colimit bridge cannot be
-- global because `HasCountableCoproducts → HasFiniteCoproducts` would create a search cycle.
local instance hasCountableCoproducts : HasCountableCoproducts C :=
  hasCountableCoproducts_of_sequentialColimits

/-- The telescope short complex of a sequential colimit filtration is short exact. -/
theorem telescopeShortExact {P : C} (F : SequentialColimitFiltration P) :
    F.telescopeShortComplex.ShortExact := sorry

end

end SequentialColimitFiltration

end CategoryTheory
