/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Grothendieck
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.Topology.Category.LCCat.Limits
public import ReasLib.Topology.Category.LCCat.SmallToSlice
public import stacks_project.Chap85.Lemma_85_21_5_Comparison
public import stacks_project.Chap85.Lemma_85_25_1_Forget
public import stacks_project.Chap85.Lemma_85_2_1_Site

/-!
# Small Zariski sites into qc slice sites

The functor `V ↦ V / U_n` from the Zariski site of a simplicial LC object to the
total qc slice site, together with the degree `-1` functor `V ↦ V / X` from the
small Zariski site of the augmentation target. These present the horizontal
morphisms of topoi in the comparison square of simplicial LC objects.
-/

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
  sorry

variable (U : SimplicialObject LCCat.{u})

/-- The functor `U_Zar ⥤ (LC_qc / U)_total` sending an open of `U_n` to that open as an
object of `LC_qc / U_n`. -/
def qcOpensOverTotal : zariskiSite (forgetToTop.obj U) ⥤ sliceTotalSite U where
  obj V := ⟨V.base, (opensOver (U.obj V.base)).obj V.opens⟩
  map {V W} f :=
    { base := f.base
      fiber :=
        Over.homMk (CategoryTheory.ObjectProperty.homMk (DiagramOpens.Hom.toContinuousMap f)) sorry }
  map_id := sorry
  map_comp := sorry

/-- On objects, `qcOpensOverTotal` sends a diagram open to the corresponding slice object. -/
theorem qcOpensOverTotal_obj (V : zariskiSite (forgetToTop.obj U)) :
    (qcOpensOverTotal U).obj V = ⟨V.base, (opensOver (U.obj V.base)).obj V.opens⟩ :=
  sorry

/-- `qcOpensOverTotal` sends `ofOpens n V` to the fibre inclusion of `opensOver.obj V`. -/
theorem qcOpensOverTotal_obj_ofOpens (n : SimplexCategoryᵒᵖ)
    (V : Opens ((forgetToTop.obj U).obj n)) :
    (qcOpensOverTotal U).obj (DiagramOpens.ofOpens (forgetToTop.obj U) n V) =
      ⟨n, (opensOver (U.obj n)).obj V⟩ :=
  sorry

/-- Stage inclusion into `U_Zar` followed by `qcOpensOverTotal` is `opensOver` into the
degree-`n` fibre of `(LC_qc / U)_total`. -/
def qcOpensOverTotal_comp_ofOpens (n : SimplexCategoryᵒᵖ) :
    DiagramOpens.fiber (forgetToTop.obj U) n ⋙ qcOpensOverTotal U ≅
      opensOver (U.obj n) ⋙ Grothendieck.ι (sliceDiagram U) n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- `qcOpensOverTotal_comp_ofOpens` is the identity on objects. -/
theorem qcOpensOverTotal_comp_ofOpens_app (n : SimplexCategoryᵒᵖ)
    (V : Opens ((forgetToTop.obj U).obj n)) :
    (qcOpensOverTotal_comp_ofOpens U n).app V = Iso.refl _ :=
  sorry

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
  sorry

end LCCat
