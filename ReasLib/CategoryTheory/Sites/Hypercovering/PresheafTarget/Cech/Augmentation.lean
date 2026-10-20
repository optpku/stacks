/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Refinement
import Mathlib.Tactic.CrossRefAttribute

/-!
# Augmented Cech complexes of presheaf-target hypercoverings

This leaf relates the augmentation of a presheaf-target hypercovering to degree-zero Cech
cohomology. The complex and cohomology objects themselves remain owned by
`HypercoveringOf.Cech`.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf.Cech

open Limits Opposite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable {G : Cᵒᵖ ⥤ Type (max w v)}

/-- Sections of a type-valued presheaf with coefficients in an abelian sheaf, represented by
morphisms from its free abelian sheafification. -/
abbrev targetSections (G : Cᵒᵖ ⥤ Type (max w v))
    (I : Sheaf J AddCommGrpCat.{max w v}) : AddCommGrpCat.{max u v w} :=
  (sectionsFunctor I).obj (op G)

/-- Target sections are morphisms from the free abelian sheaf on the target presheaf. -/
theorem targetSections_eq (G : Cᵒᵖ ⥤ Type (max w v))
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    targetSections G I = ((J.freeAbelianSheaf G : Sheaf J AddCommGrpCat.{max w v}) ⟶ I) := sorry

/-- The degree-zero cochain map induced contravariantly by the hypercovering augmentation. -/
abbrev augmentationMap (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    targetSections G I ⟶ (complex K I).X 0 :=
  (sectionsFunctor I).map K.zeroMap.op

/-- A degree-one face induces a coface map from degree zero to degree one in the sections
complex. -/
abbrev faceMap (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : Fin 2) :
    (complex K I).X 0 ⟶ (complex K I).X 1 :=
  (sectionsFunctor I).map
    (Limits.FormalCoproduct.toPresheaf.map (K.simplicial.δ i)).op

/-- The augmented degree-zero map equalizes the two degree-one coface maps. -/
theorem augmentationMap_condition (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    augmentationMap K I ≫ faceMap K I 0 =
      augmentationMap K I ≫ faceMap K I 1 := sorry

/-- The canonical fork from target sections to the two degree-one coface maps. -/
def zeroFork (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    Fork (faceMap K I 0) (faceMap K I 1) :=
  Fork.ofι (augmentationMap K I) (augmentationMap_condition K I)

/-- The leg of `zeroFork` is the map induced by the hypercovering augmentation. -/
@[simp]
theorem zeroFork_ι (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    (zeroFork K I).ι = augmentationMap K I := sorry

/-- The canonical degree-zero fork satisfies the two-coface equalizer relation. -/
theorem zeroFork_condition (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    (zeroFork K I).ι ≫ faceMap K I 0 =
      (zeroFork K I).ι ≫ faceMap K I 1 := sorry

/-- Lemma 25.6.2 [stacks 09VV]: degree-zero Cech cohomology of a hypercovering of a presheaf is
canonically isomorphic to the sections of that presheaf. -/
@[stacks 09VV "degree-zero presheaf-target hypercovering Cech cohomology"]
theorem cohomology_zero_isomorphic_targetSections
    (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    IsIsomorphic (cohomology K I 0) (targetSections G I) := sorry

end CategoryTheory.HypercoveringOf.Cech

/- The `sorryAx` contribution to `zeroFork` is confined to the proposition-valued commutativity
field supplied by `augmentationMap_condition`; its vertex and leg are explicit. -/
