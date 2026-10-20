/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Colimit.Concrete
public import ReasLib.CategoryTheory.Limits.Types.Filtered.Representatives
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stage representatives in presheaf-target hypercovering Cech cohomology

The Cech cohomology groups of hypercoverings of a fixed presheaf form a filtered diagram after
maps are identified up to simplicial homotopy.  This leaf provides the canonical colimit, its
stage maps, and the representative/common-refinement API for elements of that colimit. The
terminal-target comparison with site cohomology lives in the separate `TerminalComparison` leaf.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf.Cech

open Limits

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

section Representatives

variable [HasWeakSheafify J AddCommGrpCat.{max w v}]

/-- The stage group represented by `K` is the universe lift of its ordinary Cech cohomology
group. -/
@[simp]
theorem stageCohomology_eq (K : HypercoveringOf J 𝒢)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    stageCohomology K I i =
      universeLift.{max u v w}.obj (cohomology K I i) := sorry

/-- A stage class represents a specified class in the refinement colimit. -/
@[stacks 09VZ "representation by a hypercovering stage"]
def Represents {K : HypercoveringOf J 𝒢}
    {I : Sheaf J AddCommGrpCat.{max w v}} {i : ℕ}
    (ξK : stageCohomology K I i) (ξ : colimitCohomology 𝒢 I i) : Prop :=
  stageMap K I i ξK = ξ

/-- Two stage classes agree after pullback to a common strict hypercovering refinement. -/
@[stacks 09VZ "agreement after a common hypercovering refinement"]
def EqualAfterRefinement {K L : HypercoveringOf J 𝒢}
    {I : Sheaf J AddCommGrpCat.{max w v}} {i : ℕ}
    (ξK : stageCohomology K I i) (ξL : stageCohomology L I i) : Prop :=
  ∃ (M : HypercoveringOf J 𝒢) (f : M ⟶ K) (g : M ⟶ L),
    ((liftedDiagram 𝒢 i).map (HypercoveringOf.refinementMap f)).app I ξK =
      ((liftedDiagram 𝒢 i).map (HypercoveringOf.refinementMap g)).app I ξL

/-- Every element of a filtered presheaf-target hypercovering Cech colimit is represented at a
single hypercovering stage. -/
@[stacks 09VZ "filtered colimit stage representative"]
theorem exists_representation
    [IsFiltered (HypercoveringOf.RefinementCategory J 𝒢)]
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    (ξ : colimitCohomology 𝒢 I i) :
    ∃ (K : HypercoveringOf J 𝒢) (ξK : stageCohomology K I i),
      Represents ξK ξ := sorry

/-- Equality of two stage classes in a filtered hypercovering Cech colimit is equivalent to
equality after a common strict refinement. -/
@[stacks 09VZ "equality after a common refinement"]
theorem stageMap_eq_stageMap_iff
    [IsFiltered (HypercoveringOf.RefinementCategory J 𝒢)]
    (K L : HypercoveringOf J 𝒢)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    (ξK : stageCohomology K I i) (ξL : stageCohomology L I i) :
    stageMap K I i ξK = stageMap L I i ξL ↔
      EqualAfterRefinement ξK ξL := sorry

end Representatives

end CategoryTheory.HypercoveringOf.Cech
