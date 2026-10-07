module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.Telescope.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Request

/-!
# Finite-cover requests on refinement telescopes

This file exposes descent of a finite-cover request on a raw telescope to one finite diagram stage.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v d r q

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace DirectedPreorderSystem.StageDiagram.Telescope

variable {δ : Type d} [Preorder δ]
variable (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
variable {J : GrothendieckTopology C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} (preord D)ᵒᵖ]
variable [∀ a : δ, EssentiallySmall.{q} (D.obj a).indexᵒᵖ]

/-- Every finite-cover request on a raw telescope fiber is transported from one diagram stage.
This is the reusable finite-stage descent statement; Chapter-specific stage predicates belong in
their own modules. -/
theorem request_descends
    (r : EssentiallySmallFiber.CoverLift.Request J (diagram D)) :
    ∃ a : δ, ∃ r₀ : EssentiallySmallFiber.CoverLift.Request J (D.obj a).diagram,
      (preord_refinement D a).mapRequest r₀ = r := sorry

end DirectedPreorderSystem.StageDiagram.Telescope

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
