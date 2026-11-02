/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Stagewise sheaf atlases of a directed affine system

The stagewise atlas and its kernel-pair diagram are formed in the category of fppf sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- The cofinal tail `{ i | i0 ≤ i }` of a directed preorder. -/
abbrev Tail (i0 : I) : Type u := { i : I // i0 ≤ i }

variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (i0 : I) (P : Presentation (D.obj (OrderDual.toDual i0)))

/-- The tail contains the base index. -/
instance instNonempty_tail : Nonempty (Tail i0) :=
  ⟨⟨i0, le_rfl⟩⟩

/-- The tail inherits directedness from the ambient preorder. -/
instance instIsDirected_tail : IsDirected (Tail i0) (· ≤ ·) where
  directed a b :=
    ⟨⟨Classical.choose (directed_of (· ≤ ·) a.1 b.1),
        le_trans a.2 (Classical.choose_spec (directed_of (· ≤ ·) a.1 b.1)).1⟩,
      (Classical.choose_spec (directed_of (· ≤ ·) a.1 b.1)).1,
      (Classical.choose_spec (directed_of (· ≤ ·) a.1 b.1)).2⟩

namespace Atlas

/-- The transition from `X_i` to the base stage, viewed as a sheaf morphism. -/
abbrev stageTransition (i : I) (hi : i0 ≤ i) :
    toSheaf.obj (D.obj (OrderDual.toDual i)) ⟶
      toSheaf.obj (D.obj (OrderDual.toDual i0)) :=
  toSheaf.map (D.map (homOfLE hi))

/-- The sheaf pullback `U_i = X_i ×_{X_i0} U_i0`. -/
def atlasStage (i : I) (hi : i0 ≤ i) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  pullback (stageTransition D i0 i hi) (atlasToSheaf P)

/-- The projection from `U_i` to the base atlas. -/
def atlasStage_snd (i : I) (hi : i0 ≤ i) :
    atlasStage D i0 P i hi ⟶
      (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj P.U :=
  pullback.snd (stageTransition D i0 i hi) (atlasToSheaf P)

/-- The projection from `U_i` to `X_i`. -/
def stageAtlas (i : I) (hi : i0 ≤ i) :
    atlasStage D i0 P i hi ⟶ toSheaf.obj (D.obj (OrderDual.toDual i)) :=
  pullback.fst (stageTransition D i0 i hi) (atlasToSheaf P)

set_option backward.isDefEq.respectTransparency false in
/-- The compatibility equation used to lift a stage transition. -/
theorem atlasStageHom_w {i j : I} (hi : i0 ≤ i) (hj : i0 ≤ j) (hij : j ≤ i) :
    stageAtlas D i0 P i hi ≫
        toSheaf.map (D.map (homOfLE hij)) ≫
        stageTransition D i0 j hj =
      atlasStage_snd D i0 P i hi ≫ atlasToSheaf P := by
  unfold stageTransition stageAtlas atlasStage_snd
  rw [← Functor.map_comp, ← Functor.map_comp, homOfLE_comp]
  exact pullback.condition

/-- The transition `U_i ⟶ U_j` induced by a later-to-earlier map `X_i ⟶ X_j`. -/
def atlasStageHom {i j : I} (hi : i0 ≤ i) (hj : i0 ≤ j) (hij : j ≤ i) :
    atlasStage D i0 P i hi ⟶ atlasStage D i0 P j hj :=
  pullback.lift
    (stageAtlas D i0 P i hi ≫
      toSheaf.map (D.map (homOfLE hij)))
    (atlasStage_snd D i0 P i hi)
    (atlasStageHom_w D i0 P hi hj hij)

/-- The first projection of a stage transition is the induced transition of atlases. -/
theorem atlasStageHom_fst {i j : I} (hi : i0 ≤ i) (hj : i0 ≤ j) (hij : j ≤ i) :
    atlasStageHom D i0 P hi hj hij ≫ stageAtlas D i0 P j hj =
      stageAtlas D i0 P i hi ≫
        toSheaf.map (D.map (homOfLE hij)) :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Identity maps in the stage atlas diagram are identities. -/
theorem atlasDiagram_map_id (i : OrderDual (Tail i0)) :
    atlasStageHom D i0 P i.2 i.2 le_rfl = 𝟙 (atlasStage D i0 P i.1 i.2) := by
  apply pullback.hom_ext <;>
    simp [atlasStageHom, stageAtlas, atlasStage_snd, atlasStage]

set_option backward.isDefEq.respectTransparency false in
/-- Composition in the stage atlas diagram agrees with categorical composition. -/
theorem atlasDiagram_map_comp {i j k : OrderDual (Tail i0)} (f : i ⟶ j) (g : j ⟶ k) :
    atlasStageHom D i0 P i.2 k.2 (leOfHom (f ≫ g : i ⟶ k)) =
      atlasStageHom D i0 P i.2 j.2 (leOfHom f) ≫
        atlasStageHom D i0 P j.2 k.2 (leOfHom g) := by
  apply pullback.hom_ext
  · simp only [atlasStageHom, stageAtlas, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, homOfLE_comp]
  · simp [atlasStageHom, atlasStage_snd, Category.assoc]

/-- The directed diagram of sheaf atlases on the cofinal tail. -/
def atlasDiagram : OrderDual (Tail i0) ⥤ Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) where
  obj i := atlasStage D i0 P i.1 i.2
  map {i j} f := atlasStageHom D i0 P i.2 j.2 (leOfHom f)
  map_id i := atlasDiagram_map_id D i0 P i
  map_comp f g := atlasDiagram_map_comp D i0 P f g

/-- The relation stage `R_i = U_i ×_{X_i} U_i`. -/
def relationStage (i : I) (hi : i0 ≤ i) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  pullback (stageAtlas D i0 P i hi) (stageAtlas D i0 P i hi)

/-- The first projection of the stagewise kernel pair. -/
def relationStageFst (i : I) (hi : i0 ≤ i) :
    relationStage D i0 P i hi ⟶ atlasStage D i0 P i hi :=
  pullback.fst _ _

/-- The second projection of the stagewise kernel pair. -/
def relationStageSnd (i : I) (hi : i0 ≤ i) :
    relationStage D i0 P i hi ⟶ atlasStage D i0 P i hi :=
  pullback.snd _ _

/-- The transition between stagewise kernel pairs. -/
def relationStageHom {i j : I} (hi : i0 ≤ i) (hj : i0 ≤ j) (hij : j ≤ i) :
    relationStage D i0 P i hi ⟶ relationStage D i0 P j hj :=
  pullback.map (stageAtlas D i0 P i hi) (stageAtlas D i0 P i hi)
    (stageAtlas D i0 P j hj) (stageAtlas D i0 P j hj)
    (atlasStageHom D i0 P hi hj hij) (atlasStageHom D i0 P hi hj hij)
    (toSheaf.map (D.map (homOfLE hij)))
    (atlasStageHom_fst D i0 P hi hj hij).symm
    (atlasStageHom_fst D i0 P hi hj hij).symm

set_option backward.isDefEq.respectTransparency false in
/-- Identity maps in the relation diagram are identities. -/
theorem relationDiagram_map_id (i : OrderDual (Tail i0)) :
    relationStageHom D i0 P i.2 i.2 le_rfl =
      𝟙 (relationStage D i0 P i.1 i.2) := by
  simp [relationStageHom, atlasDiagram_map_id D i0 P i, relationStage]

set_option backward.isDefEq.respectTransparency false in
/-- Composition in the relation diagram agrees with categorical composition. -/
theorem relationDiagram_map_comp {i j k : OrderDual (Tail i0)} (f : i ⟶ j) (g : j ⟶ k) :
    relationStageHom D i0 P i.2 k.2 (leOfHom (f ≫ g : i ⟶ k)) =
      relationStageHom D i0 P i.2 j.2 (leOfHom f) ≫
        relationStageHom D i0 P j.2 k.2 (leOfHom g) := by
  apply pullback.hom_ext <;>
    simp [relationStageHom, atlasDiagram_map_comp D i0 P f g, Category.assoc]

/-- The directed diagram of stagewise kernel pairs. -/
def relationDiagram : OrderDual (Tail i0) ⥤ Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) where
  obj i := relationStage D i0 P i.1 i.2
  map {i j} f := relationStageHom D i0 P i.2 j.2 (leOfHom f)
  map_id i := relationDiagram_map_id D i0 P i
  map_comp f g := relationDiagram_map_comp D i0 P f g

/-- The first kernel-pair projections commute with transitions of atlas stages. -/
theorem relationDiagramFst_naturality ⦃i j : OrderDual (Tail i0)⦄ (f : i ⟶ j) :
    (relationDiagram D i0 P).map f ≫ relationStageFst D i0 P j.1 j.2 =
      relationStageFst D i0 P i.1 i.2 ≫ (atlasDiagram D i0 P).map f :=
  pullback.lift_fst _ _ _

/-- The second kernel-pair projections commute with transitions of atlas stages. -/
theorem relationDiagramSnd_naturality ⦃i j : OrderDual (Tail i0)⦄ (f : i ⟶ j) :
    (relationDiagram D i0 P).map f ≫ relationStageSnd D i0 P j.1 j.2 =
      relationStageSnd D i0 P i.1 i.2 ≫ (atlasDiagram D i0 P).map f :=
  pullback.lift_snd _ _ _

/-- The first projection is a natural transformation of relation diagrams. -/
def relationDiagramFst : relationDiagram D i0 P ⟶ atlasDiagram D i0 P where
  app i := relationStageFst D i0 P i.1 i.2
  naturality := relationDiagramFst_naturality D i0 P

/-- The second projection is a natural transformation of relation diagrams. -/
def relationDiagramSnd : relationDiagram D i0 P ⟶ atlasDiagram D i0 P where
  app i := relationStageSnd D i0 P i.1 i.2
  naturality := relationDiagramSnd_naturality D i0 P

end Atlas

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
