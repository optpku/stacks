/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Diagram.Operations

/-!
# Scheduled saturation data

This leaf owns terminal witnesses and bottom-indexed scheduled diagrams,
together with the constructors needed to pass between them.  Projection and
extensionality lemmas live in `Scheduled.Computations`.
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

/-- A terminal saturation witness for an arbitrary family of requests from one base
stage.  It retains both the target stage and the compatible map that realizes every request. -/
structure Terminal
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) where
  /-- The stage at which every scheduled request is realized. -/
  stage : Stage.{u, v, q, r, r'} (J := J) S P x y
  /-- The compatible refinement from the base stage to the terminal stage. -/
  hom : A ⟶ stage
  /-- Every request in the prescribed family is realized after transport. -/
  realizes : ∀ m : M, (hom.mapRequest (request m)).is_realized

namespace Terminal

variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- Package an explicit terminal-stage existence statement as terminal saturation data. -/
noncomputable def ofExists
    (hterminal :
      ∃ B : Stage.{u, v, q, r, r'} (J := J) S P x y,
        ∃ f : A ⟶ B, ∀ m : M, (f.mapRequest (request m)).is_realized) :
    Terminal (J := J) A request where
  stage := Classical.choose hterminal
  hom := Classical.choose (Classical.choose_spec hterminal)
  realizes := Classical.choose_spec (Classical.choose_spec hterminal)

end Terminal

/-- A coherent bottom-indexed diagram of saturation stages that realizes request `m`
at the stage indexed by `m`.  The underlying based diagram remains available through
`toDiagram`; this structure is the owner of the additional schedule invariant. -/
structure Diagram
    [Preorder M]
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J)
    extends Stage.Diagram (J := J) A (WithBot M) where
  /-- The base map at the request's index realizes that request. -/
  realizesAt : ∀ m : M,
    ((toDiagram.fromBase (m : WithBot M)).mapRequest (request m)).is_realized

namespace Diagram

variable [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- Add the schedule realization invariant to an existing coherent stage diagram. -/
def ofDiagram
    (D : Stage.Diagram (J := J) A (WithBot M))
    (hreal : ∀ m : M,
      ((D.fromBase (m : WithBot M)).mapRequest (request m)).is_realized) :
    Diagram (J := J) A request where
  toDiagram := D
  realizesAt := hreal

/-- The constant scheduled diagram induced by one compatible stage that realizes every request. -/
noncomputable def constant
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized) :
    Diagram (J := J) A request :=
  ofDiagram (J := J) (A := A) (request := request)
    (Stage.Diagram.constant (J := J) (A := A) (κ := WithBot M) B f) hreal

/-- Turn terminal saturation data into its constant scheduled diagram. -/
noncomputable def ofTerminal (T : Terminal (J := J) A request) :
    Diagram (J := J) A request :=
  constant (J := J) (A := A) (request := request) T.stage T.hom T.realizes

/-- Scheduled realization persists from its designated index to every later diagram index. -/
theorem realizesAt_of_le (D : Diagram (J := J) A request)
    {m : M} {i : WithBot M} (hmi : (m : WithBot M) ≤ i) :
    ((D.toDiagram.fromBase i).mapRequest (request m)).is_realized := sorry

namespace toTerminal

/-- The top component of a scheduled diagram realizes every request. -/
theorem realizes [OrderTop M] (D : Diagram (J := J) A request) :
    ∀ m : M,
      ((D.toDiagram.fromBase (⊤ : WithBot M)).mapRequest (request m)).is_realized := sorry

end toTerminal

/-- A scheduled diagram on a preorder with a greatest request index yields terminal data. -/
noncomputable def toTerminal [OrderTop M] (D : Diagram (J := J) A request) :
    Terminal (J := J) A request where
  stage := D.toDiagram.stage (⊤ : WithBot M)
  hom := D.toDiagram.fromBase (⊤ : WithBot M)
  realizes := toTerminal.realizes D

end Diagram

/- Data audit: the constructors above retain their selected stages, morphisms, and underlying
diagrams. Any `sorryAx` dependency is confined to proposition-valued realization or coherence
fields. -/

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
