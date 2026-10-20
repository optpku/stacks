/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Basic

/-!
# Arbitrary-cut extensions of scheduled saturation diagrams

This file owns the neutral datum for adjoining a stage at an arbitrary cut.
The input is the based diagram on strict predecessors; a cocone in `Under A`
simultaneously records the new stage, its base leg, and all compatible
predecessor legs.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type z} [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

/-- Data for adjoining one stage at an arbitrary cut to a based diagram on
the strict predecessors. The cocone in `Under A` owns the new stage together
with its compatible predecessor and base legs. -/
structure CutExtension (request : M → A.target.Request J) {cut : WithTop (WithBot M)}
    (D : Stage.Diagram (J := J) A {i : WithTop (WithBot M) // i < cut}) where
  /-- The based cocone from the strict-predecessor diagram to the new stage. -/
  cocone : Limits.Cocone (Under.lift D.functor D.base)
  /-- Every request scheduled strictly before the cut is realized at the new stage. -/
  realizesBefore : ∀ (m : M), ((m : WithBot M) : WithTop (WithBot M)) < cut →
    (cocone.pt.hom.mapRequest (request m)).is_realized

variable {cut : WithTop (WithBot M)}
variable {D : Stage.Diagram (J := J) A {i : WithTop (WithBot M) // i < cut}}

/-- The new saturation stage carried by an arbitrary-cut extension. -/
abbrev CutExtension.stage (extension : CutExtension (request := request) D) :
    Stage.{u, v, q, r, r'} (J := J) S P x y :=
  extension.cocone.pt.right

/-- The compatible refinement from the original base stage to the extension stage. -/
abbrev CutExtension.fromBase (extension : CutExtension (request := request) D) :
    A ⟶ extension.stage :=
  extension.cocone.pt.hom

/-- The compatible leg from one strict predecessor to the new stage. -/
abbrev CutExtension.leg (extension : CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    D.stage i ⟶ extension.stage :=
  (extension.cocone.ι.app i).right

/-- The constant open prefix represented by the new stage of an arbitrary-cut extension.

This bridge retains the extension's realization invariant while presenting its new stage
through the reusable `OpenPrefix` interface. -/
noncomputable def CutExtension.constantPrefix (extension : CutExtension (request := request) D) :
    OpenPrefix (J := J) A request cut :=
  OpenPrefix.constant (J := J) (A := A) (request := request)
    extension.stage extension.fromBase extension.realizesBefore

variable {D : Stage.Diagram (J := J) A
  {i : WithTop (WithBot M) // i < (⊤ : WithTop (WithBot M))}}

/-- At the top cut, the extension invariant realizes every scheduled request. -/
theorem CutExtension.terminalRealizes (extension : CutExtension (request := request) D) :
    ∀ m : M,
      (Stage.Hom.mapRequest (J := J) extension.fromBase (request m)).is_realized := sorry

/-- An extension at the top cut gives explicit terminal saturation data. -/
noncomputable def CutExtension.toTerminal (extension : CutExtension (request := request) D) :
    Stage.Scheduled.Terminal (J := J) A request where
  stage := extension.stage
  hom := extension.fromBase
  realizes := CutExtension.terminalRealizes (request := request) extension

/- The non-Prop content of an extension and its terminal adapter is stored
explicitly by the cocone in `Under A`. -/

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
