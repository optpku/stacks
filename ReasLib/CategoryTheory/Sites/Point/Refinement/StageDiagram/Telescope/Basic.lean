/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.Basic

/-!
# Telescopes of refinement-stage diagrams

This file owns the unquotiented telescope index and diagram, the stage-inclusion API, and the
directed telescope and its canonical cocone.  Request descent is kept in a separate leaf.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v d r

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace DirectedPreorderSystem.StageDiagram

namespace Telescope

variable {δ : Type d} [Preorder δ]

/-- The unquotiented index of a directed stage diagram.  Unlike the ordered direct limit, it
retains the stage coordinate of every representative; this is the correct owner for telescopes
whose successive occurrences must remain distinct. -/
abbrev Index (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) : Type (max d r) :=
  Σ a : δ, (D.obj a).index

/-- The preorder relation on the unquotiented telescope index. -/
def relation (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    (x y : Index D) : Prop :=
  ∃ h : x.1 ≤ y.1, D.index_map h x.2 ≤ y.2

/-- Reflexivity of the telescope comparison relation. -/
theorem relation_refl (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    (x : Index D) : relation D x x := sorry

/-- Transitivity of the telescope comparison relation. -/
theorem relation_trans (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    {x y z : Index D} : relation D x y → relation D y z → relation D x z := sorry

/-- The bundled preorder carried by the unquotiented telescope index.  The local instance here
is deliberately internal to the bundle: different stage diagrams can induce different orders on
the same raw sigma type, so this must not be a global instance. -/
noncomputable def preord (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) : Preord :=
  letI : Preorder (Index D) := {
    le := relation D
    lt := fun x y => relation D x y ∧ ¬ relation D y x
    le_refl := relation_refl D
    le_trans := fun _ _ _ => relation_trans D
    lt_iff_le_not_ge := sorry
  }
  Preord.of (Index D)

/-- The telescope index is directed when the diagram-stage preorder is directed. -/
theorem directed (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    [IsDirectedOrder δ] : IsDirected (preord D) (· ≤ ·) := sorry

/-- The object represented by one telescope index. -/
def obj (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (x : Index D) : C :=
  (D.obj x.1).diagram.obj (Opposite.op x.2)

/-- The transition map attached to one preorder comparison of telescope indices. -/
noncomputable def map (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    {x y : Index D} (h : relation D x y) : obj D y ⟶ obj D x :=
  let hstage := Classical.choose h
  let hindex := Classical.choose_spec h
  (D.obj y.1).diagram.map (Quiver.Hom.op (homOfLE hindex)) ≫
    (D.map hstage).restrictionIso.inv.app (Opposite.op x.2)

/-- Telescope transition maps send identity arrows to identity morphisms. -/
theorem map_id (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    (x : (preord D)ᵒᵖ) :
    map D (leOfHom (𝟙 x).unop) = 𝟙 (obj D x.unop) := sorry

/-- Telescope transition maps respect composition. -/
theorem map_comp (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    {X Y Z : (preord D)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map D (leOfHom (f ≫ g).unop) =
      map D (leOfHom f.unop) ≫ map D (leOfHom g.unop) := sorry

/-- The inverse-system diagram on the unquotiented telescope index. -/
noncomputable def diagram (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) :
    (preord D)ᵒᵖ ⥤ C where
  obj x := obj D x.unop
  map f := map D (leOfHom f.unop)
  map_id := map_id D
  map_comp f g := map_comp D f g

/-! The following stage-inclusion API is intentionally available before imposing directedness on
the diagram index.  The raw telescope preorder and its inverse-system diagram are already defined
at that level; directedness is only needed to package them as a `DirectedPreorderSystem`. -/

variable (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)

/-- The canonical embedding of one stage index into the bundled telescope preorder. -/
def preord_inclusion (a : δ) : (D.obj a).index ↪o preord D where
  toFun := fun i => show Index D from ⟨a, i⟩
  inj' := sorry
  map_rel_iff' := sorry

/-- A `preord_inclusion` sends an index to its matching telescope representative. -/
@[simp] theorem preord_inclusion_apply (a : δ) (i : (D.obj a).index) :
    preord_inclusion D a i = ⟨a, i⟩ := sorry

/-- Stage inclusions are monotone along every diagram transition. -/
theorem preord_inclusion_natural {a b : δ} (hab : a ≤ b) (i : (D.obj a).index) :
    preord_inclusion D a i ≤ preord_inclusion D b (D.index_map hab i) := sorry

/-- The componentwise identity isomorphism from a stage system to the raw telescope diagram
restricted along its canonical inclusion. -/
noncomputable def preord_inclusion_app (a : δ) (X : (D.obj a).indexᵒᵖ) :
    (D.obj a).diagram.obj X ≅
      (((preord_inclusion D a).toOrderHom.toFunctor).op ⋙ diagram D).obj X :=
  Iso.refl _

/-- The componentwise raw telescope inclusion is natural in the stage index. -/
theorem preord_inclusion_natural_map (a : δ) :
    ∀ {X Y : (D.obj a).indexᵒᵖ} (f : X ⟶ Y),
      (D.obj a).diagram.map f ≫ (preord_inclusion_app D a Y).hom =
        (preord_inclusion_app D a X).hom ≫
          (((preord_inclusion D a).toOrderHom.toFunctor).op ⋙ diagram D).map f := sorry

/-- The canonical identification of a stage system with the corresponding restriction of the raw
telescope diagram. -/
noncomputable def preord_inclusion_iso (a : δ) :
    (D.obj a).diagram ≅
      ((preord_inclusion D a).toOrderHom.toFunctor).op ⋙ diagram D :=
  NatIso.ofComponents (fun X => preord_inclusion_app D a X)
    (preord_inclusion_natural_map D a)

/-- The ordered refinement from one stage into the raw telescope diagram.  This does not require
the stage-index preorder to be directed. -/
noncomputable def preord_refinement (a : δ) :
    OrderedRefinement (D.obj a).diagram (diagram D) :=
  OrderedRefinement.ofEmbedding (preord_inclusion D a) (diagram D)
    (preord_inclusion_iso D a)

end Telescope

/-- The directed inverse-system telescope of a directed diagram of ordered refinements.  This
retains representatives instead of taking the quotient direct limit, which is essential for
sequential and transfinite constructions that track a particular stage. -/
noncomputable def telescope {δ : Type d} [Preorder δ] [IsDirectedOrder δ]
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) :
    DirectedPreorderSystem.{u, v, max d r} C where
  index := Telescope.preord D
  directed := Telescope.directed D
  diagram := Telescope.diagram D

namespace Telescope

variable {δ : Type d} [Preorder δ] [IsDirectedOrder δ]
variable (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)

/-- The directed-telescope form of `preord_inclusion`. -/
noncomputable abbrev inclusion (a : δ) : (D.obj a).index ↪o D.telescope.index :=
  preord_inclusion D a

/-- A directed telescope inclusion sends an index to its matching representative. -/
@[simp] theorem inclusion_apply (a : δ) (i : (D.obj a).index) :
    inclusion D a i = ⟨a, i⟩ := sorry

/-- Directed telescope inclusions are monotone along diagram transitions. -/
theorem inclusion_natural {a b : δ} (hab : a ≤ b) (i : (D.obj a).index) :
    inclusion D a i ≤ inclusion D b (D.index_map hab i) := sorry

/-- The directed-telescope form of `preord_inclusion_app`. -/
noncomputable abbrev inclusion_app (a : δ) (X : (D.obj a).indexᵒᵖ) :
    (D.obj a).diagram.obj X ≅
      (((inclusion D a).toOrderHom.toFunctor).op ⋙ D.telescope.diagram).obj X :=
  preord_inclusion_app D a X

/-- Directed telescope inclusion components are natural in the stage index. -/
theorem inclusion_natural_map (a : δ) :
    ∀ {X Y : (D.obj a).indexᵒᵖ} (f : X ⟶ Y),
      (D.obj a).diagram.map f ≫ (inclusion_app D a Y).hom =
        (inclusion_app D a X).hom ≫
          (((inclusion D a).toOrderHom.toFunctor).op ⋙ D.telescope.diagram).map f := sorry

/-- The directed-telescope form of `preord_inclusion_iso`. -/
noncomputable abbrev inclusion_iso (a : δ) :
    (D.obj a).diagram ≅
      ((inclusion D a).toOrderHom.toFunctor).op ⋙ D.telescope.diagram :=
  preord_inclusion_iso D a

/-- The directed-telescope form of `preord_refinement`. -/
noncomputable abbrev refinement (a : δ) :
    OrderedRefinement (D.obj a).diagram D.telescope.diagram :=
  preord_refinement D a

/-- Telescope refinements form a cocone over the original stage diagram. -/
theorem refinement_comp {a b : δ} (hab : a ≤ b) :
    (D.map hab).comp (refinement D b) = refinement D a := sorry

/-- The canonical cocone of a stage diagram into its unquotiented telescope. -/
noncomputable def cocone : DirectedPreorderSystem.StageDiagram.Cocone D where
  vertex := D.telescope
  leg := refinement D
  leg_comp := refinement_comp D

end Telescope

end DirectedPreorderSystem.StageDiagram

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
