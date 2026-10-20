/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Grothendieck
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.Topology.Category.LCCat.Limits
public import ReasLib.Topology.Category.LCCat.SmallToSlice
public import ReasLib.CategoryTheory.Sites.Simplicial.Slice
public import ReasLib.Topology.Category.LCCat.Simplicial
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Site

/-!
# Small Zariski sites into qc slice sites

The functor `V ↦ V / U_n` from the Zariski site of a simplicial LC object to the
total qc slice site, together with the degree `-1` functor `V ↦ V / X` from the
small Zariski site of the augmentation target. These present the horizontal
morphisms of topoi in the comparison square of simplicial LC objects.
-/

-- The public comparison functors use private arrow maps and law proofs.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject
open Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace LCCat

variable (X : LCCat.{u})

/-- Inverse image of type-valued sheaves along `opensOver X` into the qc slice site
preserves finite limits. -/
instance opensOver_qc_sheafPullback_preservesFiniteLimits
    [HasWeakSheafify (qcTopology.over X) (Type u)]
    [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u, (opensOver X).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((opensOver X).sheafPullback (Type u) (Opens.grothendieckTopology X.obj)
        (qcTopology.over X)) :=
  sorry

/-- The morphism of topoi `h₋₁ : Sh(LC_qc / X) ⟶ Sh(X)` presented by `opensOver X`. -/
def opensOverQcTopos
    [HasWeakSheafify (qcTopology.over X) (Type u)]
    [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u, (opensOver X).op.HasLeftKanExtension P] :
    MorphismOfTopoiIn (Opens.grothendieckTopology X.obj) (qcTopology.over X) :=
  (opensOver X).morphismOfTopoiInOfContinuous
    (Opens.grothendieckTopology X.obj) (qcTopology.over X)

/-- Inverse image of `opensOverQcTopos` is qc sheaf pullback along `opensOver`. -/
theorem opensOverQcTopos_inverseImage
    [HasWeakSheafify (qcTopology.over X) (Type u)]
    [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u, (opensOver X).op.HasLeftKanExtension P] :
    (opensOverQcTopos X)⁻¹ = SmallToSlice.qcTypePullback X :=
  rfl

variable (U : SimplicialObject LCCat.{u})

/-- Restricted continuous maps commute with their inclusions into the ambient stage. -/
private theorem qcOpensOverTotal_map_w {V W : zariskiSite (forgetToTop.obj U)}
    (f : V ⟶ W) :
    CategoryTheory.ObjectProperty.homMk (DiagramOpens.Hom.toContinuousMap f) ≫
        ((opensOver (U.obj W.base)).obj W.opens).hom =
      ((Over.map (U.map f.base)).obj ((opensOver (U.obj V.base)).obj V.opens)).hom := by
  sorry

/-- The arrow of total slices induced by a restricted continuous map between diagram opens. -/
private def qcOpensOverTotalMap {V W : zariskiSite (forgetToTop.obj U)} (f : V ⟶ W) :
    (⟨V.base, (opensOver (U.obj V.base)).obj V.opens⟩ : sliceTotalSite U) ⟶
      ⟨W.base, (opensOver (U.obj W.base)).obj W.opens⟩ :=
  { base := f.base
    fiber := Over.homMk
      (CategoryTheory.ObjectProperty.homMk (DiagramOpens.Hom.toContinuousMap f))
      (qcOpensOverTotal_map_w U f) }

/-- The restricted continuous-map arrows preserve identities and composition. -/
private theorem qcOpensOverTotal_map_laws :
    (∀ V : zariskiSite (forgetToTop.obj U),
      qcOpensOverTotalMap U (𝟙 V) = 𝟙 _) ∧
    (∀ {V W Z : zariskiSite (forgetToTop.obj U)} (f : V ⟶ W) (g : W ⟶ Z),
      qcOpensOverTotalMap U (f ≫ g) = qcOpensOverTotalMap U f ≫ qcOpensOverTotalMap U g) := by
  sorry

/-- The functor from diagram opens to total qc slices sends an open in each degree to
that open as an object over the same stage. -/
def qcOpensOverTotal : zariskiSite (forgetToTop.obj U) ⥤ sliceTotalSite U where
  obj V := ⟨V.base, (opensOver (U.obj V.base)).obj V.opens⟩
  map f := qcOpensOverTotalMap U f
  map_id := (qcOpensOverTotal_map_laws U).1
  map_comp := (qcOpensOverTotal_map_laws U).2

/-- On objects, `qcOpensOverTotal` sends a diagram open to the corresponding slice object. -/
theorem qcOpensOverTotal_obj (V : zariskiSite (forgetToTop.obj U)) :
    (qcOpensOverTotal U).obj V = ⟨V.base, (opensOver (U.obj V.base)).obj V.opens⟩ :=
  rfl

/-- `qcOpensOverTotal` sends `ofOpens n V` to the fibre inclusion of `opensOver.obj V`. -/
theorem qcOpensOverTotal_obj_ofOpens (n : SimplexCategoryᵒᵖ)
    (V : Opens ((forgetToTop.obj U).obj n)) :
    (qcOpensOverTotal U).obj (DiagramOpens.ofOpens (forgetToTop.obj U) n V) =
      ⟨n, (opensOver (U.obj n)).obj V⟩ :=
  rfl

/-- Identity components identify the stagewise comparison maps naturally. -/
private theorem qcOpensOverTotal_comp_ofOpens_naturality (n : SimplexCategoryᵒᵖ)
    {V W : Opens ((forgetToTop.obj U).obj n)} (f : V ⟶ W) :
    (DiagramOpens.fiber (forgetToTop.obj U) n ⋙ qcOpensOverTotal U).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (opensOver (U.obj n) ⋙ Grothendieck.ι (sliceDiagram U) n).map f := by
  sorry

/-- Stage inclusion into `U_Zar` followed by `qcOpensOverTotal` is `opensOver` into the
degree-`n` fibre of `(LC_qc / U)_total`. -/
def qcOpensOverTotal_comp_ofOpens (n : SimplexCategoryᵒᵖ) :
    DiagramOpens.fiber (forgetToTop.obj U) n ⋙ qcOpensOverTotal U ≅
      opensOver (U.obj n) ⋙ Grothendieck.ι (sliceDiagram U) n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun f ↦ qcOpensOverTotal_comp_ofOpens_naturality U n f)

/-- `qcOpensOverTotal_comp_ofOpens` is the identity on objects. -/
theorem qcOpensOverTotal_comp_ofOpens_app (n : SimplexCategoryᵒᵖ)
    (V : Opens ((forgetToTop.obj U).obj n)) :
    (qcOpensOverTotal_comp_ofOpens U n).app V = Iso.refl _ :=
  rfl

/-- The functor `qcOpensOverTotal` is continuous for the Zariski topology of `U` and the
total qc slice topology. -/
instance qcOpensOverTotal_isContinuous :
    (qcOpensOverTotal U).IsContinuous (zariskiTopology (forgetToTop.obj U))
      (sliceTotalTopology qcTopology U) :=
  sorry

/-- Inverse image of type-valued sheaves along `qcOpensOverTotal` preserves finite limits. -/
instance qcOpensOverTotal_sheafPullback_preservesFiniteLimits
    [HasWeakSheafify (sliceTotalTopology qcTopology U) (Type u)]
    [∀ P : (zariskiSite (forgetToTop.obj U))ᵒᵖ ⥤ Type u,
      (qcOpensOverTotal U).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((qcOpensOverTotal U).sheafPullback (Type u) (zariskiTopology (forgetToTop.obj U))
        (sliceTotalTopology qcTopology U)) :=
  sorry

/-- The morphism of topoi `h : Sh((LC_qc / U)_total) ⟶ Sh(U_Zar)` presented by
`qcOpensOverTotal`. -/
def qcOpensOverTotalTopos
    [HasWeakSheafify (sliceTotalTopology qcTopology U) (Type u)]
    [∀ P : (zariskiSite (forgetToTop.obj U))ᵒᵖ ⥤ Type u,
      (qcOpensOverTotal U).op.HasLeftKanExtension P] :
    MorphismOfTopoiIn (zariskiTopology (forgetToTop.obj U))
      (sliceTotalTopology qcTopology U) :=
  (qcOpensOverTotal U).morphismOfTopoiInOfContinuous
    (zariskiTopology (forgetToTop.obj U)) (sliceTotalTopology qcTopology U)

/-- Inverse image of `qcOpensOverTotalTopos` is sheaf pullback along `qcOpensOverTotal`. -/
theorem qcOpensOverTotalTopos_inverseImage
    [HasWeakSheafify (sliceTotalTopology qcTopology U) (Type u)]
    [∀ P : (zariskiSite (forgetToTop.obj U))ᵒᵖ ⥤ Type u,
      (qcOpensOverTotal U).op.HasLeftKanExtension P] :
    (qcOpensOverTotalTopos U)⁻¹ =
      (qcOpensOverTotal U).sheafPullback (Type u) (zariskiTopology (forgetToTop.obj U))
        (sliceTotalTopology qcTopology U) :=
  rfl

end LCCat
