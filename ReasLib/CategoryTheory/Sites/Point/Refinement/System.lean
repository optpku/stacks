/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.System.Basic

/-!
# Directed preorder systems from diagrams

This leaf packages a diagram indexed by a directed preorder as the neutral
`DirectedPreorderSystem` used by refinement and saturation constructions.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

namespace DirectedPreorderSystem

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]

/-- Package a diagram indexed by a directed preorder as a directed preorder
system.  Nonemptiness is deliberately not required. -/
def ofDiagram (S : ιᵒᵖ ⥤ C) [IsDirected ι (· ≤ ·)] :
    DirectedPreorderSystem.{u, v, r} C where
  index := Preord.of ι
  directed := inferInstance
  diagram := S

namespace ofDiagram

/-- The index of the directed preorder system associated to a diagram is its
original index. -/
@[simp]
theorem index (S : ιᵒᵖ ⥤ C) [IsDirected ι (· ≤ ·)] :
    (ofDiagram S).index = Preord.of ι := sorry

/-- The diagram of the directed preorder system associated to a diagram is the
original diagram. -/
@[simp]
theorem diagram (S : ιᵒᵖ ⥤ C) [IsDirected ι (· ≤ ·)] :
    (ofDiagram S).diagram = S := sorry

/-- Essential smallness of a diagram index is available through the associated
directed preorder system. -/
instance instEssentiallySmall (S : ιᵒᵖ ⥤ C)
    [IsDirected ι (· ≤ ·)] [EssentiallySmall.{q} ιᵒᵖ] :
    EssentiallySmall.{q} (ofDiagram S).indexᵒᵖ :=
  inferInstanceAs (EssentiallySmall.{q} ιᵒᵖ)

/-- Presheaf-fiber colimit support for a diagram is available through the
associated directed preorder system. -/
instance instFiberHasColimits (S : ιᵒᵖ ⥤ C)
    [IsDirected ι (· ≤ ·)] [LocallySmall.{q} C]
    [EssentiallySmall.{q} ιᵒᵖ]
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)] :
    HasColimitsOfShape
      (EssentiallySmallFiber.fiber (ofDiagram S).diagram).Elementsᵒᵖ (Type q) :=
  inferInstanceAs
    (HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q))

end ofDiagram

end DirectedPreorderSystem

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
