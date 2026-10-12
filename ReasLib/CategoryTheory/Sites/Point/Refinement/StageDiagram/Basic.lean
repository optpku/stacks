/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.System.Basic

/-!
# Directed diagrams of inverse-system refinements

This file owns the lower directed-stage diagram, its transition maps on indices, and the
corresponding notion of a refinement cocone.  It deliberately imposes neither directedness on the
stage preorder nor nonemptiness or smallness on the individual stage indices.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v d r r'

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace DirectedPreorderSystem

/-- A coherent diagram of directed preorder systems connected by pure order-embedding
refinements.  This is the minimal layer for directed-union constructions: individual stage indices
need not yet be nonempty or essentially small. -/
structure StageDiagram (δ : Type d) [Preorder δ]
    (C : Type u) [Category.{v} C] where
  /-- The directed preorder system at each diagram stage. -/
  obj : δ → DirectedPreorderSystem.{u, v, r} C
  /-- The pure refinement associated to an order relation of diagram stages. -/
  map : ∀ {a b : δ}, a ≤ b → OrderedRefinement (obj a).diagram (obj b).diagram
  /-- Transition refinements are identities at each diagram stage. -/
  map_refl : ∀ a : δ, map (a := a) (b := a) le_rfl = OrderedRefinement.id (obj a).diagram
  /-- Transition refinements compose along comparable triples of diagram stages. -/
  map_comp : ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
    map (le_trans hab hbc) = (map hab).comp (map hbc)

namespace StageDiagram

variable {δ : Type d} [Preorder δ]
variable (D : StageDiagram.{u, v, d, r} δ C)

/-- Lower stage diagrams are determined by their stage systems and transition
refinements; the identity and composition laws are proposition-valued. -/
@[ext]
theorem ext {D E : StageDiagram.{u, v, d, r} δ C}
    (hobj : D.obj = E.obj)
    (hmap : HEq
      (fun {a b : δ} (hab : a ≤ b) ↦ D.map hab)
      (fun {a b : δ} (hab : a ≤ b) ↦ E.map hab)) :
    D = E := sorry

/-- The order embedding between stage indices induced by a diagram transition. -/
def index_map {a b : δ} (hab : a ≤ b) :
    (D.obj a).index ↪o (D.obj b).index :=
  (D.map hab).embedding

/-- The index map of a reflexive stage comparison is the identity function. -/
theorem index_map_refl (D : StageDiagram.{u, v, d, r} δ C) (a : δ)
    (i : (D.obj a).index) :
    D.index_map (a := a) (b := a) le_rfl i = i := sorry

/-- Index maps respect composition of stage comparisons. -/
theorem index_map_comp (D : StageDiagram.{u, v, d, r} δ C)
    {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c) (i : (D.obj a).index) :
    D.index_map hbc (D.index_map hab i) = D.index_map (le_trans hab hbc) i := sorry

/-- A cocone of pure ordered refinements out of a lower stage diagram.  No stage or vertex
nonemptiness/smallness is required at this layer. -/
structure Cocone (D : StageDiagram.{u, v, d, r} δ C) where
  /-- The directed preorder system receiving all stage refinements. -/
  vertex : DirectedPreorderSystem.{u, v, r'} C
  /-- The pure refinement from each stage into the vertex. -/
  leg : ∀ a : δ, OrderedRefinement (D.obj a).diagram vertex.diagram
  /-- Each leg agrees with the composite along a diagram transition. -/
  leg_comp : ∀ {a b : δ} (hab : a ≤ b),
    (D.map hab).comp (leg b) = leg a

/-- Refinement cocones are determined by their vertex and legs; compatibility
with diagram transitions is proposition-valued. -/
@[ext]
theorem Cocone.ext {D : StageDiagram.{u, v, d, r} δ C}
    {Q R : Cocone.{u, v, d, r, r'} D}
    (hvertex : Q.vertex = R.vertex) (hleg : HEq Q.leg R.leg) :
    Q = R := sorry

end StageDiagram

end DirectedPreorderSystem

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
