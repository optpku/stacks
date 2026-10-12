/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Const
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap85.Lemma_85_21_5_Comparison
public import stacks_project.Chap85.Remark_85_4_1_Fiberwise

/-!
# Augmentation of a simplicial slice site

An augmentation `a : U ⟶ const X` induces the cocontinuous functor
`V / U_n ↦ V / X` on `(C / U)_total`, presenting a morphism of topoi
`Sh((C / U)_total) ⟶ Sh(C / X)`. The degree-zero map `Over.map (a.app (op ⦋0⦌))`
is an augmentation in the sense of Remark 85.4.1.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped Simplicial

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The cocontinuous functor `(C / U)_total ⥤ C / X` sending `V / U_n` to `V / X`,
assembled from the fiber functors `Over.map (a.app n)` and naturality of `a`. -/
def sliceForget {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    sliceTotalSite U ⥤ Over X where
  obj Y := (Over.map (a.app Y.base)).obj Y.fiber
  map {Y Z} f :=
    ((Over.mapCongr (a.app Y.base) (U.map f.base ≫ a.app Z.base)
          ((Category.comp_id (a.app Y.base)).symm.trans (a.naturality f.base).symm)).hom ≫
        (Over.mapComp (U.map f.base) (a.app Z.base)).hom).app Y.fiber ≫
      (Over.map (a.app Z.base)).map f.fiber
  map_id := sorry
  map_comp := sorry

/-- On objects, `sliceForget a` is postcomposition with the component `a.app n`. -/
theorem sliceForget_obj {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (Y : sliceTotalSite U) :
    (sliceForget U a).obj Y = (Over.map (a.app Y.base)).obj Y.fiber :=
  sorry

/-- The total presenting functor assembled from the common composites
`u_n = Over.map (a.app (op ⦋0⦌)) ∘ Over.map (U.map (const ⦋0⦌ n 0).op)`, the
cocontinuous form of the Remark 85.4.1 (A) equalizer `u_φ ∘ u0`. -/
def sliceForget_ofAugmentation {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    sliceTotalSite U ⥤ Over X where
  obj Y :=
    (Over.map
        (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫ a.app (op ⦋0⦌))).obj
      Y.fiber
  map {Y Z} f :=
    ((Over.mapCongr
          (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫ a.app (op ⦋0⦌))
          (U.map f.base ≫
            (U.map (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op ≫ a.app (op ⦋0⦌)))
          (((a.naturality (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op).trans
              (Category.comp_id (a.app Y.base))).trans
            (((a.naturality f.base).trans (Category.comp_id (a.app Y.base))).symm.trans
              (congrArg (fun t ↦ U.map f.base ≫ t)
                ((a.naturality (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op).trans
                  (Category.comp_id (a.app Z.base))).symm)))).hom ≫
        (Over.mapComp (U.map f.base)
          (U.map (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op ≫
            a.app (op ⦋0⦌))).hom).app Y.fiber ≫
      (Over.map
          (U.map (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op ≫
            a.app (op ⦋0⦌))).map f.fiber
  map_id := sorry
  map_comp := sorry

/-- On objects, `sliceForget_ofAugmentation` is the common composite through degree zero. -/
theorem sliceForget_ofAugmentation_obj {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (Y : sliceTotalSite U) :
    (sliceForget_ofAugmentation U a).obj Y =
      (Over.map
          (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫
            a.app (op ⦋0⦌))).obj Y.fiber :=
  sorry

/-- `sliceForget` and `sliceForget_ofAugmentation` agree by naturality of `a` along the
constant operators `⦋0⦌ ⟶ n`. -/
def sliceForget_iso_ofAugmentation {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    sliceForget U a ≅ sliceForget_ofAugmentation U a :=
  NatIso.ofComponents
    (fun Y ↦
      (Over.mapCongr (a.app Y.base)
          (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫ a.app (op ⦋0⦌))
          ((a.naturality (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op).trans
            (Category.comp_id (a.app Y.base))).symm).app Y.fiber)
    sorry

variable (J : GrothendieckTopology C)
variable {X : C} (U : SimplicialObject C)
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
variable [HasPullbacks C]

/-- Remark 85.4.1 (A) up to isomorphism: the composites of `Over.pullback (a.app (op ⦋0⦌))`
with `Over.pullback` of two operators `φ, ψ : ⦋0⦌ ⟶ n` agree via `Over.pullbackComp`
and naturality of `a`. -/
def slicePullback_compIso {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n) :
    Over.pullback (a.app (op ⦋0⦌)) ⋙ Over.pullback (U.map φ.op) ≅
      Over.pullback (a.app (op ⦋0⦌)) ⋙ Over.pullback (U.map ψ.op) :=
  (Over.pullbackComp (U.map φ.op) (a.app (op ⦋0⦌))).symm ≪≫
    conjugateIsoEquiv (Over.mapPullbackAdj (U.map φ.op ≫ a.app (op ⦋0⦌)))
        (Over.mapPullbackAdj (U.map ψ.op ≫ a.app (op ⦋0⦌)))
        (Over.mapCongr (U.map φ.op ≫ a.app (op ⦋0⦌)) (U.map ψ.op ≫ a.app (op ⦋0⦌))
          (((a.naturality φ.op).trans (Category.comp_id (a.app (op n)))).trans
            (((a.naturality ψ.op).trans (Category.comp_id (a.app (op n)))).symm))).symm ≪≫
    Over.pullbackComp (U.map ψ.op) (a.app (op ⦋0⦌))

/-- `slicePullback_compIso` is the `Over.pullbackComp` comparison of the two composites. -/
theorem slicePullback_compIso_eq {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n) :
    slicePullback_compIso U a φ ψ =
      (Over.pullbackComp (U.map φ.op) (a.app (op ⦋0⦌))).symm ≪≫
        conjugateIsoEquiv (Over.mapPullbackAdj (U.map φ.op ≫ a.app (op ⦋0⦌)))
            (Over.mapPullbackAdj (U.map ψ.op ≫ a.app (op ⦋0⦌)))
            (Over.mapCongr (U.map φ.op ≫ a.app (op ⦋0⦌)) (U.map ψ.op ≫ a.app (op ⦋0⦌))
              (((a.naturality φ.op).trans (Category.comp_id (a.app (op n)))).trans
                (((a.naturality ψ.op).trans (Category.comp_id (a.app (op n)))).symm))).symm ≪≫
        Over.pullbackComp (U.map ψ.op) (a.app (op ⦋0⦌)) :=
  sorry

/-- The Case A continuous presenting functor `C / X ⥤ (C / U)_total`, sending `V / X`
to the degree-zero object `V ×_X U_0 / U_0`. -/
def sliceAugmentationPullback : Over X ⥤ sliceTotalSite U :=
  Over.pullback (a.app (op ⦋0⦌)) ⋙ Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)

/-- On objects, `sliceAugmentationPullback` is fibre product with `U_0`, included in
degree zero. -/
theorem sliceAugmentationPullback_obj (V : Over X) :
    (sliceAugmentationPullback U a).obj V =
      ⟨op ⦋0⦌, (Over.pullback (a.app (op ⦋0⦌))).obj V⟩ :=
  sorry

/-- `Over.pullback (a.app (op ⦋0⦌))` is continuous for the slice precoverages. -/
instance slicePullback_precoverage_isContinuous :
    Functor.Precoverage.IsContinuous (Over.pullback (a.app (op ⦋0⦌)))
      (J.over X).toPrecoverage (slicePrecoverage J U (op ⦋0⦌)) :=
  sorry

/-- The Case A presenting functor `sliceAugmentationPullback` is continuous for the
total topology. -/
instance sliceAugmentationPullback_isContinuous :
    (sliceAugmentationPullback U a).IsContinuous (J.over X) (sliceTotalTopology J U) :=
  sorry

/-- The localization `a0 : C / U_0 ⥤ C / X` is an augmentation of the slice diagram in the
cocontinuous presentation of Remark 85.4.1. -/
instance sliceDiagram_isAugmentation :
    Grothendieck.IsAugmentation (sliceDiagram U) (slicePrecoverage J U)
      (J.over X).toPrecoverage (Over.map (a.app (op ⦋0⦌))) :=
  sorry

/-- The functor `V / U_n ↦ V / X` is cocontinuous for the total and slice topologies. -/
instance sliceForget_isCocontinuous :
    (sliceForget U a).IsCocontinuous (sliceTotalTopology J U) (J.over X) :=
  sorry

/-- The stage-composite presenting functor is cocontinuous for the total and slice topologies. -/
instance sliceForget_ofAugmentation_isCocontinuous :
    (sliceForget_ofAugmentation U a).IsCocontinuous
      (sliceTotalTopology J U) (J.over X) :=
  sorry

variable [HasSheafify (sliceTotalTopology J U) (Type w)]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type w, (sliceForget U a).op.HasPointwiseRightKanExtension P]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type w,
    (sliceForget_ofAugmentation U a).op.HasPointwiseRightKanExtension P]

/-- The morphism of topoi `a : Sh((C / U)_total) ⟶ Sh(C / X)` presented by `sliceForget`. -/
def sliceAugmentationTopos :
    MorphismOfTopoiIn (J.over X) (sliceTotalTopology J U) :=
  (sliceForget U a).morphismOfTopoiInOfCocontinuous (sliceTotalTopology J U) (J.over X)

/-- Inverse image of `sliceAugmentationTopos` is cocontinuous sheaf pullback along
`sliceForget`. -/
theorem sliceAugmentationTopos_inverseImage :
    (sliceAugmentationTopos J U a).inverseImage =
      (sliceForget U a).sheafPullbackCocontinuous (Type w)
        (sliceTotalTopology J U) (J.over X) :=
  sorry

/-- The total morphism of topoi induced by the Remark 85.4.1 (A) augmentation, presented
by the common composites `u_n = u_φ ∘ u0` in the cocontinuous `Over.map` form identified
with `Over.pullback` by Sites Lemma 7.27.3. -/
def sliceAugmentationTopos_ofAugmentation :
    MorphismOfTopoiIn (J.over X) (sliceTotalTopology J U) :=
  (sliceForget_ofAugmentation U a).morphismOfTopoiInOfCocontinuous
    (sliceTotalTopology J U) (J.over X)

/-- Direct image of `sliceAugmentationTopos_ofAugmentation` is cocontinuous sheaf
pushforward along `sliceForget_ofAugmentation`. -/
theorem sliceAugmentationTopos_ofAugmentation_pushforward :
    (sliceAugmentationTopos_ofAugmentation J U a).pushforward =
      (sliceForget_ofAugmentation U a).sheafPushforwardCocontinuous (Type w)
        (sliceTotalTopology J U) (J.over X) :=
  sorry

/-- `sliceAugmentationTopos` and `sliceAugmentationTopos_ofAugmentation` have canonically
isomorphic direct images. -/
def sliceAugmentation_pushforwardIso :
    (sliceAugmentationTopos J U a).pushforward ≅
      (sliceAugmentationTopos_ofAugmentation J U a).pushforward :=
  Functor.sheafPushforwardCocontinuousIso (sliceTotalTopology J U) (J.over X)
    (sliceForget U a) (sliceForget_iso_ofAugmentation U a)

/-- Base change along `a0 : U_0 ⟶ X` is continuous on slice sites. -/
instance slicePullback_isContinuous :
    (Over.pullback (a.app (op ⦋0⦌))).IsContinuous
      (J.over X) (J.over (U.obj (op ⦋0⦌))) :=
  sorry

/-- Localization `Over.map a0` is cocontinuous on slice sites. -/
instance sliceMap_isCocontinuous :
    (Over.map (a.app (op ⦋0⦌))).IsCocontinuous
      (J.over (U.obj (op ⦋0⦌))) (J.over X) :=
  sorry

variable [HasWeakSheafify (J.over X) (Type w)]
variable [HasWeakSheafify (J.over (U.obj (op ⦋0⦌))) (Type w)]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type w,
    (Over.pullback (a.app (op ⦋0⦌))).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((Over.pullback (a.app (op ⦋0⦌))).sheafPullback (Type w)
      (J.over X) (J.over (U.obj (op ⦋0⦌))))]
variable [∀ P : (Over (U.obj (op ⦋0⦌)))ᵒᵖ ⥤ Type w,
    (Over.map (a.app (op ⦋0⦌))).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (J.over (U.obj (op ⦋0⦌))) (Type w)]

/-- Remark 85.4.1 (A): `Over.pullback (a.app (op ⦋0⦌))` presents the same morphism of
topoi `Sh(C / U_0) ⟶ Sh(C / X)` as the cocontinuous functor
`Over.map (a.app (op ⦋0⦌))`, by Sites Lemma 7.27.3. -/
noncomputable def slicePullback_presents_augmentation :
    J.overMapPushforward (Type w) (a.app (op ⦋0⦌)) ≅
      (Over.map (a.app (op ⦋0⦌))).sheafPushforwardCocontinuous (Type w)
        (J.over (U.obj (op ⦋0⦌))) (J.over X) :=
  J.overMapPushforwardIsoCocontinuous (Type w) (a.app (op ⦋0⦌))

/-- `slicePullback_presents_augmentation` is the Sites Lemma 7.27.3 comparison on
`a.app (op ⦋0⦌)`. -/
theorem slicePullback_presents_augmentation_eq :
    slicePullback_presents_augmentation J U a =
      J.overMapPushforwardIsoCocontinuous (Type w) (a.app (op ⦋0⦌)) :=
  sorry

end CategoryTheory.SimplicialObject
