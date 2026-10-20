/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Atlas

/-!
# Comparison of a presentation quotient with a directed sheaf limit

This module constructs the limiting atlas, relation, coequalizer, and comparison morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

open AlgebraicSpace Atlas

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (i0 : I) (P : Presentation (D.obj (OrderDual.toDual i0)))

/-- A chosen upper bound of two indices in a directed preorder. -/
def directedBound (a b : I) : I :=
  Classical.choose (directed_of (· ≤ ·) a b)

/-- The chosen upper bound is at least its first argument. -/
theorem directedBound_le_left (a b : I) : a ≤ directedBound a b :=
  (Classical.choose_spec (directed_of (· ≤ ·) a b)).1

/-- The chosen upper bound is at least its second argument. -/
theorem directedBound_le_right (a b : I) : b ≤ directedBound a b :=
  (Classical.choose_spec (directed_of (· ≤ ·) a b)).2

/-- The inverse limit of the sheaf-valued algebraic-space diagram. -/
def sheafLimit : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  limit (D ⋙ toSheaf)

/-- The projection from the sheaf limit to a stage. -/
def sheafLimit_π (i : OrderDual I) :
    sheafLimit D ⟶ toSheaf.obj (D.obj i) :=
  limit.π (D ⋙ toSheaf) i

/-- The inverse limit of the stagewise sheaf atlases on the cofinal tail. -/
def limitAtlas : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  limit (Atlas.atlasDiagram D i0 P)

/-- The projection from the limiting atlas to a stage. -/
def limitAtlas_π (i : I) (hi : i0 ≤ i) :
    limitAtlas D i0 P ⟶ Atlas.atlasStage D i0 P i hi :=
  limit.π (Atlas.atlasDiagram D i0 P) (OrderDual.toDual ⟨i, hi⟩)

/-- The composite from the limiting atlas to a stage of the original system. -/
def limitAtlasToStageSheaf (i : I) (hi : i0 ≤ i) :
    limitAtlas D i0 P ⟶ toSheaf.obj (D.obj (OrderDual.toDual i)) :=
  limitAtlas_π D i0 P i hi ≫ Atlas.stageAtlas D i0 P i hi

/-- The relation diagram obtained from the stagewise kernel pairs. -/
def limitRelation : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  limit (Atlas.relationDiagram D i0 P)

/-- The first map from the limiting relation to the limiting atlas. -/
def limitRelationFst :
    limitRelation D i0 P ⟶ limitAtlas D i0 P :=
  limMap (Atlas.relationDiagramFst D i0 P)

/-- The second map from the limiting relation to the limiting atlas. -/
def limitRelationSnd :
    limitRelation D i0 P ⟶ limitAtlas D i0 P :=
  limMap (Atlas.relationDiagramSnd D i0 P)

/-- The coequalizer of the two limiting relation projections. -/
def limitQuotient : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  coequalizer (limitRelationFst D i0 P) (limitRelationSnd D i0 P)

/-- The quotient map from the limiting atlas to its coequalizer. -/
def limitQuotientMap :
    limitAtlas D i0 P ⟶ limitQuotient D i0 P :=
  coequalizer.π (limitRelationFst D i0 P) (limitRelationSnd D i0 P)

/-- The component of the atlas cone at an arbitrary index. -/
def coneFromLimitAtlas_π (j : OrderDual I) :
    limitAtlas D i0 P ⟶ (D ⋙ toSheaf).obj j :=
  limitAtlasToStageSheaf D i0 P (directedBound i0 (OrderDual.ofDual j))
      (directedBound_le_left i0 (OrderDual.ofDual j)) ≫
    toSheaf.map (D.map (homOfLE (directedBound_le_right i0 (OrderDual.ofDual j))))

/-- The tail component of the atlas cone is its stage projection. -/
theorem coneFromLimitAtlas_π_tail (i : Tail i0) :
    coneFromLimitAtlas_π D i0 P (OrderDual.toDual i) =
      limitAtlasToStageSheaf D i0 P i.1 i.2 :=
  sorry

/-- Naturality of the atlas cone components. -/
theorem coneFromLimitAtlas_naturality ⦃j j' : OrderDual I⦄ (f : j ⟶ j') :
    ((Functor.const (OrderDual I)).obj (limitAtlas D i0 P)).map f ≫
        coneFromLimitAtlas_π D i0 P j' =
      coneFromLimitAtlas_π D i0 P j ≫ (D ⋙ toSheaf).map f :=
  sorry

/-- The cone from the limiting atlas to the original sheaf diagram. -/
def coneFromLimitAtlas : Cone (D ⋙ toSheaf) where
  pt := limitAtlas D i0 P
  π :=
    { app := coneFromLimitAtlas_π D i0 P
      naturality := coneFromLimitAtlas_naturality D i0 P }

/-- The canonical map from the limiting atlas to the sheaf limit. -/
def limitAtlasToSheafLimit :
    limitAtlas D i0 P ⟶ sheafLimit D :=
  limit.lift (D ⋙ toSheaf) (coneFromLimitAtlas D i0 P)

/-- The limiting relation is the kernel pair of the canonical atlas map. -/
theorem limitRelation_isKernelPair :
    IsKernelPair (limitAtlasToSheafLimit D i0 P)
      (limitRelationFst D i0 P) (limitRelationSnd D i0 P) :=
  sorry

/-- The canonical map from the limiting atlas to the sheaf limit is an epimorphism. -/
theorem limitAtlasToSheafLimit_epi : Epi (limitAtlasToSheafLimit D i0 P) :=
  sorry

/-- The canonical atlas map equalizes the two limiting relation projections. -/
theorem limitAtlasToSheafLimit_equalizes :
    limitRelationFst D i0 P ≫ limitAtlasToSheafLimit D i0 P =
      limitRelationSnd D i0 P ≫ limitAtlasToSheafLimit D i0 P :=
  sorry

/-- The comparison from the limiting quotient to the sheaf limit. -/
def quotientToSheafLimit :
    limitQuotient D i0 P ⟶ sheafLimit D :=
  coequalizer.desc (limitAtlasToSheafLimit D i0 P)
    (limitAtlasToSheafLimit_equalizes D i0 P)

/-- The comparison factors the quotient map through the atlas map. -/
theorem quotientToSheafLimit_spec :
    limitQuotientMap D i0 P ≫ quotientToSheafLimit D i0 P =
      limitAtlasToSheafLimit D i0 P :=
  coequalizer.π_desc _ _

/-- The comparison has the expected projection at every stage. -/
theorem quotientToSheafLimit_π (i : OrderDual I) :
    limitQuotientMap D i0 P ≫ quotientToSheafLimit D i0 P ≫ sheafLimit_π D i =
      coneFromLimitAtlas_π D i0 P i :=
  sorry

/-- The comparison from the quotient of the limiting atlas to the sheaf limit is an isomorphism. -/
theorem quotientToSheafLimit_isIso
    [h_affine : ∀ {i i' : I} (h : i ≤ i'), AlgebraicSpace.Affine (D.map (homOfLE h))] :
    IsIso (quotientToSheafLimit D i0 P) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
