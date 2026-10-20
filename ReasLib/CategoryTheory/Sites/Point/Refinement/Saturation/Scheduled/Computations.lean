/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Basic

/-!
# Computations for scheduled saturation diagrams

This file records extensionality and the projection API for the scheduled
diagram constructors and terminal adapters.
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

namespace Terminal

variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- Terminal saturation witnesses with the same stage and compatible map are equal. -/
@[ext]
theorem ext {T U : Terminal (J := J) A request}
    (hstage : T.stage = U.stage) (hhom : HEq T.hom U.hom) :
    T = U := sorry

/-- Recover the existential terminal-stage specification carried by a terminal witness. -/
theorem toExists (T : Terminal (J := J) A request) :
    ∃ B : Stage.{u, v, q, r, r'} (J := J) S P x y,
      ∃ f : A ⟶ B, ∀ m : M, (f.mapRequest (request m)).is_realized := sorry

/-- The morphism selected from terminal-stage existence data realizes every
request in the prescribed family. -/
@[simp]
theorem ofExists.realizes
    (hterminal :
      ∃ B : Stage.{u, v, q, r, r'} (J := J) S P x y,
        ∃ f : A ⟶ B, ∀ m : M, (f.mapRequest (request m)).is_realized)
    (m : M) :
    (((ofExists (J := J) hterminal).hom).mapRequest (request m)).is_realized := sorry

end Terminal

namespace Diagram

variable [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- Scheduled diagrams with the same underlying based diagram are equal. -/
@[ext]
theorem ext {D E : Diagram (J := J) A request}
    (h : D.toDiagram = E.toDiagram) :
    D = E := sorry

/-- Forgetting the schedule invariant from `ofDiagram D hreal` recovers `D`. -/
@[simp]
theorem ofDiagram.toDiagram
    (D : Stage.Diagram (J := J) A (WithBot M))
    (hreal : ∀ m : M,
      ((D.fromBase (m : WithBot M)).mapRequest (request m)).is_realized) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram = D := sorry

/-- The stage of `ofDiagram D hreal` at an index is the corresponding stage of `D`. -/
@[simp]
theorem ofDiagram.stage
    (D : Stage.Diagram (J := J) A (WithBot M))
    (hreal : ∀ m : M,
      ((D.fromBase (m : WithBot M)).mapRequest (request m)).is_realized)
    (i : WithBot M) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.stage i =
      D.stage i := sorry

/-- A transition of `ofDiagram D hreal` is the corresponding transition of `D`. -/
@[simp]
theorem ofDiagram.hom
    (D : Stage.Diagram (J := J) A (WithBot M))
    (hreal : ∀ m : M,
      ((D.fromBase (m : WithBot M)).mapRequest (request m)).is_realized)
    {i j : WithBot M} (hij : i ≤ j) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.hom hij =
      D.hom hij := sorry

/-- A base leg of `ofDiagram D hreal` is the corresponding base leg of `D`. -/
@[simp]
theorem ofDiagram.fromBase
    (D : Stage.Diagram (J := J) A (WithBot M))
    (hreal : ∀ m : M,
      ((D.fromBase (m : WithBot M)).mapRequest (request m)).is_realized)
    (i : WithBot M) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.fromBase i =
      D.fromBase i := sorry

/-- The based diagram underlying a constant scheduled diagram is the corresponding constant
based diagram. -/
@[simp]
theorem constant.toDiagram
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized) :
    (constant (J := J) (request := request) B f hreal).toDiagram =
      Stage.Diagram.constant (J := J) (A := A) (κ := WithBot M) B f := sorry

/-- Every stage of a constant scheduled diagram is its chosen target stage. -/
@[simp]
theorem constant.stage
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized)
    (i : WithBot M) :
    (constant (J := J) (request := request) B f hreal).toDiagram.stage i = B := sorry

/-- Every transition of a constant scheduled diagram is the identity of its target stage. -/
@[simp]
theorem constant.hom
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized)
    {i j : WithBot M} (hij : i ≤ j) :
    (constant (J := J) (request := request) B f hreal).toDiagram.hom hij =
      𝟙 B := sorry

/-- Every base leg of a constant scheduled diagram is its chosen compatible map. -/
@[simp]
theorem constant.fromBase
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized)
    (i : WithBot M) :
    (constant (J := J) (request := request) B f hreal).toDiagram.fromBase i = f := sorry

/-- The based diagram underlying `ofTerminal T` is constant at the terminal stage and map of
`T`. -/
@[simp]
theorem ofTerminal.toDiagram (T : Terminal (J := J) A request) :
    (ofTerminal (J := J) T).toDiagram =
      Stage.Diagram.constant (J := J) (A := A) (κ := WithBot M) T.stage T.hom := sorry

/-- Every stage of the scheduled diagram induced by `T` is `T.stage`. -/
@[simp]
theorem ofTerminal.stage (T : Terminal (J := J) A request) (i : WithBot M) :
    (ofTerminal (J := J) T).toDiagram.stage i = T.stage := sorry

/-- Every transition of the scheduled diagram induced by `T` is the identity of `T.stage`. -/
@[simp]
theorem ofTerminal.hom (T : Terminal (J := J) A request)
    {i j : WithBot M} (hij : i ≤ j) :
    (ofTerminal (J := J) T).toDiagram.hom hij = 𝟙 T.stage := sorry

/-- Every base leg of the scheduled diagram induced by `T` is `T.hom`. -/
@[simp]
theorem ofTerminal.fromBase (T : Terminal (J := J) A request) (i : WithBot M) :
    (ofTerminal (J := J) T).toDiagram.fromBase i = T.hom := sorry

/-- The terminal stage extracted from a scheduled diagram is its stage at the greatest index. -/
@[simp]
theorem toTerminal.stage [OrderTop M] (D : Diagram (J := J) A request) :
    (toTerminal D).stage = D.toDiagram.stage (⊤ : WithBot M) := sorry

/-- The compatible map of the extracted terminal witness is the base leg at the greatest
index. -/
@[simp]
theorem toTerminal.hom [OrderTop M] (D : Diagram (J := J) A request) :
    (toTerminal D).hom = D.toDiagram.fromBase (⊤ : WithBot M) := sorry

/-- Extracting terminal data from the constant diagram induced by that data recovers the
original terminal witness. -/
@[simp]
theorem toTerminal.ofTerminal [OrderTop M]
    (T : Terminal (J := J) A request) :
    toTerminal (ofTerminal (J := J) T) = T := sorry

end Diagram

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
