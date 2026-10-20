/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Basic

/-!
# Operations on scheduled saturation prefixes

This file supplies restriction and terminal/global-diagram adapters for closed
and open scheduled saturation prefixes.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

namespace Stage.Scheduled

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type z}

local notation "Ω" => WithBot M
local notation "Cut" => WithTop Ω

namespace Prefix

variable [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- The closed-prefix index inclusion is monotone. -/
theorem restrictIndex.monotone {cut cut' : Ω} (hcut : cut' ≤ cut) :
    Monotone (fun i : {i : Ω // i ≤ cut'} =>
      (⟨i.1, le_trans i.2 hcut⟩ : {i : Ω // i ≤ cut})) := sorry

/-- The order homomorphism from a smaller closed initial segment into a larger one. -/
def restrictIndex {cut cut' : Ω} (hcut : cut' ≤ cut) :
    {i : Ω // i ≤ cut'} →o {i : Ω // i ≤ cut} where
  toFun := fun i => ⟨i.1, le_trans i.2 hcut⟩
  monotone' := restrictIndex.monotone hcut

/-- The based stage diagram obtained by restricting a closed prefix. -/
noncomputable def restrictDiagram {cut cut' : Ω}
    (D : Prefix (J := J) A request cut) (hcut : cut' ≤ cut) :
    Stage.Diagram (J := J) A {i : Ω // i ≤ cut'} :=
  Stage.Diagram.reindex (J := J) D.toDiagram (restrictIndex hcut)

/-- The restricted closed-prefix diagram realizes every request below its new cut. -/
theorem restrict.realizes {cut cut' : Ω}
    (D : Prefix (J := J) A request cut) (hcut : cut' ≤ cut) :
    ∀ (m : M) (hm : (m : Ω) ≤ cut'),
      (((restrictDiagram D hcut).fromBase ⟨(m : Ω), hm⟩).mapRequest
        (request m)).is_realized := sorry

/-- Restrict a closed prefix to a smaller initial segment. -/
noncomputable def restrict {cut cut' : Ω}
    (D : Prefix (J := J) A request cut) (hcut : cut' ≤ cut) :
    Prefix (J := J) A request cut' :=
  ofDiagram (J := J) (A := A) (request := request)
    (restrictDiagram D hcut) (restrict.realizes D hcut)

/-- The index embedding into a greatest closed prefix is monotone. -/
theorem scheduledIndex.monotone {cut : Ω} (hcut : ∀ i : Ω, i ≤ cut) :
    Monotone (fun i => (⟨i, hcut i⟩ : {i : Ω // i ≤ cut})) := sorry

/-- Embed every scheduling index into a greatest closed prefix as an order
homomorphism. -/
def scheduledIndex {cut : Ω} (hcut : ∀ i : Ω, i ≤ cut) :
    Ω →o {i : Ω // i ≤ cut} where
  toFun := fun i => ⟨i, hcut i⟩
  monotone' := scheduledIndex.monotone hcut

/-- Reindex a greatest closed prefix over the full scheduling preorder. -/
noncomputable def scheduledStageDiagram {cut : Ω}
    (D : Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut) :
    Stage.Diagram (J := J) A Ω :=
  Stage.Diagram.reindex (J := J) D.toDiagram (scheduledIndex hcut)

/-- The fully reindexed diagram realizes every request at its scheduling index. -/
theorem toScheduledDiagram.realizes {cut : Ω}
    (D : Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut) :
    ∀ m : M,
      (((scheduledStageDiagram D hcut).fromBase (m : Ω)).mapRequest
        (request m)).is_realized := sorry

/-- Reindex a closed prefix to a global scheduled diagram when its cut bounds
every scheduling index. -/
noncomputable def toScheduledDiagram {cut : Ω}
    (D : Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut) :
    Stage.Scheduled.Diagram (J := J) A request :=
  Stage.Scheduled.Diagram.ofDiagram (J := J) (A := A) (request := request)
    (scheduledStageDiagram D hcut) (toScheduledDiagram.realizes D hcut)

end Prefix

namespace OpenPrefix

variable [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- The open-prefix index inclusion is monotone. -/
theorem restrictIndex.monotone {cut cut' : Cut} (hcut : cut' ≤ cut) :
    Monotone (fun i : {i : Cut // i ≤ cut'} =>
      (⟨i.1, le_trans i.2 hcut⟩ : {i : Cut // i ≤ cut})) := sorry

/-- The order homomorphism from a smaller open initial segment into a larger one. -/
def restrictIndex {cut cut' : Cut} (hcut : cut' ≤ cut) :
    {i : Cut // i ≤ cut'} →o {i : Cut // i ≤ cut} where
  toFun := fun i => ⟨i.1, le_trans i.2 hcut⟩
  monotone' := restrictIndex.monotone hcut

/-- The based stage diagram obtained by restricting an open prefix. -/
noncomputable def restrictDiagram {cut cut' : Cut}
    (D : OpenPrefix (J := J) A request cut) (hcut : cut' ≤ cut) :
    Stage.Diagram (J := J) A {i : Cut // i ≤ cut'} :=
  Stage.Diagram.reindex (J := J) D.toDiagram (restrictIndex hcut)

/-- The restricted open-prefix diagram retains the strict realization invariant. -/
theorem restrict.realizes {cut cut' : Cut}
    (D : OpenPrefix (J := J) A request cut) (hcut : cut' ≤ cut) :
    ∀ (i : {j : Cut // j ≤ cut'}) (m : M), ((m : Ω) : Cut) < i.1 →
      (((restrictDiagram D hcut).fromBase i).mapRequest (request m)).is_realized := sorry

/-- Restrict an open prefix to a smaller cut. -/
noncomputable def restrict {cut cut' : Cut}
    (D : OpenPrefix (J := J) A request cut) (hcut : cut' ≤ cut) :
    OpenPrefix (J := J) A request cut' :=
  ofDiagram (J := J) (A := A) (request := request)
    (restrictDiagram D hcut) (restrict.realizes D hcut)

/-- The top node of a terminal open prefix realizes every scheduled request. -/
theorem toTerminal.realizes
    (D : OpenPrefix (J := J) A request (⊤ : Cut)) :
    ∀ m : M,
      ((D.toDiagram.fromBase ⟨⊤, le_rfl⟩).mapRequest (request m)).is_realized := sorry

/-- A terminal open prefix yields explicit terminal data by evaluating at its
adjoined top node. -/
noncomputable def toTerminal
    (D : OpenPrefix (J := J) A request (⊤ : Cut)) :
    Stage.Scheduled.Terminal (J := J) A request where
  stage := D.toDiagram.stage ⟨⊤, le_rfl⟩
  hom := D.toDiagram.fromBase ⟨⊤, le_rfl⟩
  realizes := toTerminal.realizes D

/-- Collapse a terminal open prefix to the constant bottom-indexed scheduled
diagram determined by its top node. -/
noncomputable def toTerminalDiagram
    (D : OpenPrefix (J := J) A request (⊤ : Cut)) :
    Stage.Scheduled.Diagram (J := J) A request :=
  Stage.Scheduled.Diagram.ofTerminal (J := J) (A := A) (request := request) D.toTerminal

end OpenPrefix

/- Restriction and adapter definitions retain their explicit index maps, stage diagrams,
and terminal data. Any `sorryAx` below is confined to monotonicity, coherence, or
request-realization propositions. -/

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
