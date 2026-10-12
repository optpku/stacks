/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement.Category

/-!
# Diagrams of refinement stages

This leaf owns the component and transition accessors for an ordinary diagram
of refinement stages, together with its canonical forgetful target diagram.
Telescope stages and their inclusions live in separate leaves.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace RefinementStage.Diagram

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {κ : Type z} [Preorder κ]

/-- The refinement stage at one index of an ordinary diagram. -/
abbrev stage (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S) (i : κ) :=
  D.obj i

/-- The compatible refinement-stage morphism attached to an order comparison. -/
abbrev hom (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {i j : κ} (hij : i ≤ j) : stage D i ⟶ stage D j :=
  D.map (homOfLE hij)

namespace hom

/-- A reflexive transition in a refinement-stage diagram is the identity morphism. -/
@[simp]
theorem refl (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S) (i : κ) :
    hom D (le_rfl : i ≤ i) = 𝟙 (stage D i) := sorry

/-- Refinement-stage diagram transitions compose along chains of indices. -/
@[simp]
theorem comp (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    hom D (le_trans hij hjk) = hom D hij ≫ hom D hjk := sorry

end hom

/-- Forget the common-source factorization from every component of a refinement-stage diagram.
The result is the canonical source-free target diagram. -/
noncomputable def toTargetDiagram (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S) :
    κ ⥤ Target.{u, v, q, r'} C :=
  D ⋙ RefinementStage.forget

namespace toTargetDiagram

/-- The target at a forgotten diagram component is the target of the original refinement stage. -/
@[simp]
theorem obj (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S) (i : κ) :
    (toTargetDiagram D).obj i = (stage D i).target := sorry

/-- A forgotten diagram transition is the target morphism underlying the original
refinement-stage morphism. -/
@[simp]
theorem map (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {i j : κ} (hij : i ≤ j) :
    (toTargetDiagram D).map (homOfLE hij) = (hom D hij).toTarget := sorry

namespace map

/-- A forgotten diagram transition retains the same ordered target refinement. -/
@[simp]
theorem toRefinement
    (D : κ ⥤ RefinementStage.{u, v, q, r, r'} S)
    {i j : κ} (hij : i ≤ j) :
    ((toTargetDiagram D).map (homOfLE hij)).toRefinement = (hom D hij).toRefinement := sorry

end map

end toTargetDiagram

end RefinementStage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
