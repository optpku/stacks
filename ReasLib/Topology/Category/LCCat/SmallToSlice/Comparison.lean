/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Abelian
public import ReasLib.Topology.Category.LCCat.Covering
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
public import ReasLib.Topology.Sheaf.BaseChange.Proper
import Mathlib.Tactic.CrossRefAttribute

/-!
# The concrete `LCCat` topology-comparison situation

This leaf owns the source-facing coefficient family for the comparison
`zarTopology ≤ qcTopology` on `LCCat`.  The primitive coefficient object is the essential image of
the canonical small-to-slice inverse image; the Situation structure is a derived package of the
five closure conditions.  No Chapter 21 declaration is imported here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open TopologicalSpace

noncomputable section

universe u

namespace LCCat.SmallToSlice

variable (X : LCCat.{u})

section ToposSquares

variable {X Y : LCCat.{u}}

/-- Lemma 21.31.8 (0D92): the inverse images from the small open sites to the Zariski
slice sites commute with pullback along `f`. -/
@[stacks 0D92 "small/Zariski inverse-image square"]
noncomputable def zarPullbackIso (f : X ⟶ Y) :
    TopCat.Sheaf.pullback (Type u) f.hom ⋙ typePullback X ≅
      typePullback Y ⋙ zarTopology.overMapPullback (Type u) f :=
  -- `isContinuous_comp` is kept explicit by the site API to avoid global search loops.
  letI : Functor.IsContinuous (Opens.map f.hom ⋙ opensOver X)
      (Opens.grothendieckTopology Y.obj) (zarTopology.over X) :=
    Functor.isContinuous_comp (Opens.map f.hom) (opensOver X)
      (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)
      (zarTopology.over X)
  letI : Functor.IsContinuous (opensOver Y ⋙ Over.pullback f)
      (Opens.grothendieckTopology Y.obj) (zarTopology.over X) :=
    Functor.isContinuous_comp (opensOver Y) (Over.pullback f)
      (Opens.grothendieckTopology Y.obj) (zarTopology.over Y) (zarTopology.over X)
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.hom)
      ((opensOver X).sheafAdjunctionContinuous (Type u)
        (Opens.grothendieckTopology X.obj) (zarTopology.over X))).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp'
        (F := Opens.map f.hom) (G := opensOver X)
        (FG := opensOver Y ⋙ Over.pullback f) (opensOver_compIso f).symm
        (Type u) (Opens.grothendieckTopology Y.obj)
        (Opens.grothendieckTopology X.obj) (zarTopology.over X) ≪≫
      (Functor.sheafPushforwardContinuousComp'
        (F := opensOver Y) (G := Over.pullback f)
        (FG := opensOver Y ⋙ Over.pullback f) (Iso.refl _)
        (Type u) (Opens.grothendieckTopology Y.obj)
        (zarTopology.over Y) (zarTopology.over X)).symm))
    (Adjunction.comp
      ((opensOver Y).sheafAdjunctionContinuous (Type u)
        (Opens.grothendieckTopology Y.obj) (zarTopology.over Y))
      (zarTopology.overMapPushforwardAdjunction (Type u) f))

/-- The composite `π_X⁻¹ ⋙ ε_X⁻¹` is canonically the inverse image induced directly by
`opensOver X` with the qc topology. -/
@[stacks 0D92 "small-to-qc comparison"]
noncomputable def qcTypePullbackComparisonIso (X : LCCat.{u})
    [HasWeakSheafify (qcTopology.over X) (Type u)] :
    typePullback X ⋙ comparisonTopologyPullback (Type u) zar_le_qc X ≅
      qcTypePullback X :=
  -- The comparison identity is a Prop-valued, topology-specific continuity pin.
  letI : Functor.IsContinuous (𝟭 (Over X)) (zarTopology.over X) (qcTopology.over X) :=
    comparisonOver_id_isContinuous zar_le_qc X
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
      ((opensOver X).sheafAdjunctionContinuous (Type u)
        (Opens.grothendieckTopology X.obj) (zarTopology.over X))
      (comparisonTopologyAdjunction (Type u) zar_le_qc X)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp'
        (F := opensOver X) (G := 𝟭 (Over X)) (FG := opensOver X)
        (Functor.rightUnitor (opensOver X)) (Type u)
        (Opens.grothendieckTopology X.obj) (zarTopology.over X)
        (qcTopology.over X)))
    ((opensOver X).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology X.obj) (qcTopology.over X))

/-- Lemma 21.31.8 (0D92): the inverse images from the small topoi to the qc slice topoi
commute with pullback along `f`. -/
@[stacks 0D92 "small/qc inverse-image square"]
noncomputable def qcPullbackIso (f : X ⟶ Y)
    [HasWeakSheafify (qcTopology.over X) (Type u)]
    [HasWeakSheafify (qcTopology.over Y) (Type u)] :
    TopCat.Sheaf.pullback (Type u) f.hom ⋙ qcTypePullback X ≅
      qcTypePullback Y ⋙ qcTopology.overMapPullback (Type u) f :=
  Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (Type u) f.hom)
      (qcTypePullbackComparisonIso X).symm ≪≫
    Functor.isoWhiskerRight (zarPullbackIso f)
      (comparisonTopologyPullback (Type u) zar_le_qc X) ≪≫
    Functor.isoWhiskerLeft (typePullback Y)
      (overMapPullbackComparisonIso (A := Type u) zar_le_qc f) ≪≫
    Functor.isoWhiskerRight (qcTypePullbackComparisonIso Y)
      (qcTopology.overMapPullback (Type u) f)

/-- The canonical direct-image comparison is the right mate of `qcPullbackIso`. It is
defined for every map; properness is used only to prove that it is invertible. -/
@[stacks 0D92 "small/qc direct-image comparison"]
noncomputable def qcPushforwardComparison (f : X ⟶ Y)
    [HasWeakSheafify (qcTopology.over X) (Type u)]
    [HasWeakSheafify (qcTopology.over Y) (Type u)] :
    TopCat.Sheaf.pushforward (Type u) f.hom ⋙ qcTypePullback Y ⟶
      qcTypePullback X ⋙ qcTopology.overMapPushforward (Type u) f :=
  CategoryTheory.DerivedBaseChange.map
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.hom)
    (qcTopology.overMapPushforwardAdjunction (Type u) f)
    (qcPullbackIso f).symm

/-- Lemma 21.31.8 (0D92): the canonical direct-image comparison is invertible when `f`
is proper. Componentwise, this is the set-valued proper base-change theorem for
`TopCat.Sheaf.BaseChange.map`. -/
@[stacks 0D92 "proper small/qc direct-image comparison"]
theorem qcPushforwardComparison_isIso_of_proper (f : X ⟶ Y)
    [HasWeakSheafify (qcTopology.over X) (Type u)]
    [HasWeakSheafify (qcTopology.over Y) (Type u)]
    (hf : IsProperMap f.hom) :
    IsIso (qcPushforwardComparison f) := sorry

end ToposSquares

/-- Lemma 21.31.9 (3): inverse image along a proper relocalization preserves `essImageAb`. -/
@[stacks 0EZI "(3) inverse-image closure"]
theorem essImageAb_inverseImage_mem
    {X Y : LCCat.{u}} (f : X ⟶ Y)
    {F : Sheaf (zarTopology.over Y) AddCommGrpCat.{u + 1}}
    (hF : essImageAb Y F) :
    essImageAb X ((zarTopology.overMapPullback AddCommGrpCat.{u + 1} f).obj F) := sorry

/-- Lemma 21.31.9 (4): an essential-image coefficient is a sheaf for the qc topology. -/
@[stacks 0EZI "(4) qc sheaf condition"]
theorem essImageAb_isSheafQc
    {F : Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1}}
    (hF : essImageAb X F) :
    Presheaf.IsSheaf (qcTopology.over X) F.1 := sorry

/-- Lemma 21.31.9 (0EZI): the qc/Zariski comparison on `LCCat`, with coefficient family
`essImageAb`, satisfies the five conditions of `TopologyComparison.Situation`. -/
@[stacks 0EZI]
theorem comparisonSituation :
    TopologyComparison.Situation qcTopology zarTopology LCCat.proper
      (fun X : LCCat.{u} ↦ essImageAb X) := sorry

end LCCat.SmallToSlice
