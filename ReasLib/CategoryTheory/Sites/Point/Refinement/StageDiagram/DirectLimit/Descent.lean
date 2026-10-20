/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.StageDiagram.DirectLimit.Basic

/-!
# Descent of refinement-stage diagrams to a direct-limit index

This file contains the quotient-representative implementation that descends the stage diagrams to
the ordered direct-limit index.  Downstream code should normally use the public colimit facade
rather than these witness-level definitions.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v d r

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace DirectedPreorderSystem.StageDiagram.Descent

variable {δ : Type d} [Preorder δ] [IsDirectedOrder δ]

/-- A representative of a point in the ordered direct limit, before descending the diagrams. -/
abbrev Raw (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) : Type (max d r) :=
  Σ a : δ, (D.obj a).index

/-- The object of the descended diagram represented by one stage index. -/
def stalk (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (x : Raw D) : C :=
  (D.obj x.1).diagram.obj (Opposite.op x.2)

/-- A transition between two representatives, computed at a common later stage. -/
noncomputable def map_at (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    (x y : Raw D) {c : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c)
    (hle : D.index_map hxc x.2 ≤ D.index_map hyc y.2) :
    stalk D y ⟶ stalk D x :=
  (D.map hyc).restrictionIso.hom.app (Opposite.op y.2) ≫
    (D.obj c).diagram.map (Quiver.Hom.op (homOfLE hle)) ≫
      (D.map hxc).restrictionIso.inv.app (Opposite.op x.2)

/-- The direct-limit comparison witness specialized to one stage diagram.  Its generic owner is
`DirectLimit.CommonStage`; this local name exposes the transition maps in diagram notation. -/
abbrev ComparisonStage (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    (x y : D.index_preord) :=
  _root_.DirectLimit.CommonStage
    (fun a b hab => D.index_map (a := a) (b := b) hab) x y

/-- A chosen semantic common-stage record for a direct-limit comparison. -/
noncomputable def comparison_stage (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    {x y : D.index_preord} (h : x ≤ y) : ComparisonStage D x y :=
  _root_.DirectLimit.commonStage
    (fun a b hab => D.index_map (a := a) (b := b) hab) h

/-- The generic quotient-representative witness specialized to a canonical stage inclusion. -/
abbrev InclusionStage (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ)
    (i : (D.obj a).index) :=
  _root_.DirectLimit.RepresentativeStage
    (fun b c hbc => D.index_map (a := b) (b := c) hbc)
    (D.index_inclusion a i) a i

/-- A chosen semantic common-stage record for a canonical inclusion. -/
noncomputable def inclusion_stage (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ)
    (i : (D.obj a).index) : InclusionStage D a i :=
  _root_.DirectLimit.representativeStage
    (fun b c hbc => D.index_map (a := b) (b := c) hbc)
    (D.index_inclusion a i) a i (D.index_inclusion_apply a i)

/-- The transition map computed at one common stage is the identity on one representative. -/
theorem map_at_id (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : Raw D)
    {c : δ} (hac : a.1 ≤ c) :
    map_at D a a hac hac le_rfl = 𝟙 (stalk D a) := sorry

/-- The raised comparison of two representatives is supplied by monotonicity of the transition. -/
theorem map_at_up_le (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (x y : Raw D)
    {c : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c)
    (hle : D.index_map hxc x.2 ≤ D.index_map hyc y.2) {e : δ} (hce : c ≤ e) :
    D.index_map (le_trans hxc hce) x.2 ≤ D.index_map (le_trans hyc hce) y.2 := sorry

/-- Raising a common-stage witness does not change the descended transition. -/
theorem map_at_up (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (x y : Raw D)
    {c : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c)
    (hle : D.index_map hxc x.2 ≤ D.index_map hyc y.2) {e : δ} (hce : c ≤ e) :
    map_at D x y (le_trans hxc hce) (le_trans hyc hce)
        (map_at_up_le D x y hxc hyc hle hce) = map_at D x y hxc hyc hle := sorry

/-- Common-stage transitions compose. -/
theorem map_at_comp (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    (x y z : Raw D) {c : δ} (hxc : x.1 ≤ c) (hyc : y.1 ≤ c) (hzc : z.1 ≤ c)
    (hxy : D.index_map hxc x.2 ≤ D.index_map hyc y.2)
    (hyz : D.index_map hyc y.2 ≤ D.index_map hzc z.2) :
    map_at D y z hyc hzc hyz ≫ map_at D x y hxc hyc hxy =
      map_at D x z hxc hzc (le_trans hxy hyz) := sorry

/-- The descended transition attached to an order comparison in the direct-limit index. -/
noncomputable def desc (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    {x y : D.index_preord} (h : x ≤ y) :
    stalk D y.out ⟶ stalk D x.out :=
  map_at D x.out y.out
    (comparison_stage D h).left_le
    (comparison_stage D h).right_le
    (comparison_stage D h).map_le

/-- The descended transition on an identity arrow is the identity. -/
theorem desc_id (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    (x : D.index_preordᵒᵖ) :
    desc D (leOfHom (𝟙 x).unop) = 𝟙 (stalk D x.unop.out) := sorry

/-- The descended transitions respect composition of arrows in the opposite index category. -/
theorem desc_comp (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C)
    {X Y Z : D.index_preordᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    desc D (leOfHom (f ≫ g).unop) =
      desc D (leOfHom f.unop) ≫ desc D (leOfHom g.unop) := sorry

/-- The inverse-system diagram descended from a directed stage diagram. -/
noncomputable def system (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) :
    D.index_preordᵒᵖ ⥤ C where
  obj x := stalk D x.unop.out
  map f := desc D (leOfHom f.unop)
  map_id := desc_id D
  map_comp := desc_comp D

/-- The forward component of the canonical isomorphism from one stage diagram to the descended
system restricted along its direct-limit inclusion. -/
noncomputable def inclusion_hom
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ)
    (i : (D.obj a).index) :
    (D.obj a).diagram.obj (Opposite.op i) ⟶
      (system D).obj (Opposite.op (D.index_inclusion a i)) :=
  map_at D (D.index_inclusion a i).out ⟨a, i⟩
    (inclusion_stage D a i).out_le
    (inclusion_stage D a i).source_le
    (le_of_eq (inclusion_stage D a i).image_eq)

/-- The inverse component of the canonical stage-to-limit isomorphism. -/
noncomputable def inclusion_inv
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ)
    (i : (D.obj a).index) :
    (system D).obj (Opposite.op (D.index_inclusion a i)) ⟶
      (D.obj a).diagram.obj (Opposite.op i) :=
  map_at D ⟨a, i⟩ (D.index_inclusion a i).out
    (inclusion_stage D a i).source_le
    (inclusion_stage D a i).out_le
    (le_of_eq (inclusion_stage D a i).image_eq.symm)

/-- The forward and inverse inclusion components cancel on a stage. -/
theorem inclusion_hom_inv
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ)
    (i : (D.obj a).index) :
    inclusion_hom D a i ≫ inclusion_inv D a i =
      𝟙 ((D.obj a).diagram.obj (Opposite.op i)) := sorry

/-- The inverse and forward inclusion components cancel on the descended system. -/
theorem inclusion_inv_hom
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ)
    (i : (D.obj a).index) :
    inclusion_inv D a i ≫ inclusion_hom D a i =
      𝟙 ((system D).obj (Opposite.op (D.index_inclusion a i))) := sorry

/-- The component isomorphism identifying a stage diagram with the restriction of the descended
system along its canonical inclusion. -/
noncomputable def inclusion_app
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ)
    (X : (D.obj a).indexᵒᵖ) :
    (D.obj a).diagram.obj X ≅
      (((D.index_inclusion a).toOrderHom.toFunctor).op ⋙ system D).obj X where
  hom := inclusion_hom D a X.unop
  inv := inclusion_inv D a X.unop
  hom_inv_id := inclusion_hom_inv D a X.unop
  inv_hom_id := inclusion_inv_hom D a X.unop

/-- The component isomorphisms of the descended system are natural in the stage index. -/
theorem inclusion_natural
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ) :
    ∀ {X Y : (D.obj a).indexᵒᵖ} (f : X ⟶ Y),
      (D.obj a).diagram.map f ≫ (inclusion_app D a Y).hom =
        (inclusion_app D a X).hom ≫
          (((D.index_inclusion a).toOrderHom.toFunctor).op ⋙ system D).map f := sorry

/-- The canonical stage-to-limit natural isomorphism, kept under the `Descent` implementation
namespace so the public `StageDiagram` surface stays compact. -/
noncomputable def iso
    (D : DirectedPreorderSystem.StageDiagram.{u, v, d, r} δ C) (a : δ) :
    (D.obj a).diagram ≅
      ((D.index_inclusion a).toOrderHom.toFunctor).op ⋙ system D :=
  NatIso.ofComponents (fun X => inclusion_app D a X)
    (inclusion_natural D a)

end DirectedPreorderSystem.StageDiagram.Descent

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
