module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint
public import stacks_project.Chap85.Lemma_85_21_5_Augmentation
public import stacks_project.Chap85.Lemma_85_25_1_OpensOver
public import stacks_project.Chap85.Lemma_85_2_4_Comparison
public import stacks_project.Chap85.Lemma_85_2_8_Morphism

/-!
# Inverse-image square of qc and Zariski augmentations

The horizontal morphisms of topoi presented by `qcOpensOverTotal` and `opensOver`
fit in a commutative inverse-image square with the Section 85.21 slice
augmentation and the Lemma 85.2.8 Zariski augmentation of a simplicial LC object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.SimplicialObject Opposite TopologicalSpace TopCat
open LCCat.SmallToSlice
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)

/-- Degree-zero continuous presenter of `a⁻¹ ⋙ h⁻¹`, sending an open of `X` to that
open as an object of `(LC_qc / U)_total`. -/
def qcOpensOver_zariskiTotalPresenter :
    Opens X.obj ⥤ sliceTotalSite U :=
  Opens.map (a.app (op ⦋0⦌)).hom ⋙
    DiagramOpens.fiber (forgetToTop.obj U) (op ⦋0⦌) ⋙ qcOpensOverTotal U

/-- `qcOpensOver_zariskiTotalPresenter` is the unfolded composite
`Opens.map ⋙ fiber ⋙ qcOpensOverTotal`. -/
theorem qcOpensOver_zariskiTotalPresenter_eq :
    qcOpensOver_zariskiTotalPresenter a =
      Opens.map (a.app (op ⦋0⦌)).hom ⋙
        DiagramOpens.fiber (forgetToTop.obj U) (op ⦋0⦌) ⋙ qcOpensOverTotal U :=
  sorry

/-- Degree-zero identification of the two composites `Opens X.obj ⥤ sliceTotalSite U`
presenting the horizontal arrows of the comparison square. -/
def qcOpensOver_presenterIso :
    opensOver X ⋙ sliceAugmentationPullback U a ≅
      qcOpensOver_zariskiTotalPresenter a :=
  (Functor.associator (opensOver X) (Over.pullback (a.app (op ⦋0⦌)))
      (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌))).symm ≪≫
    isoWhiskerRight (opensOver_compIso (a.app (op ⦋0⦌)))
      (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)) ≪≫
    Functor.associator (Opens.map (a.app (op ⦋0⦌)).hom) (opensOver (U.obj (op ⦋0⦌)))
      (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)) ≪≫
    isoWhiskerLeft (Opens.map (a.app (op ⦋0⦌)).hom)
      (qcOpensOverTotal_comp_ofOpens U (op ⦋0⦌)).symm ≪≫
    (Functor.associator (Opens.map (a.app (op ⦋0⦌)).hom)
        (DiagramOpens.fiber (forgetToTop.obj U) (op ⦋0⦌)) (qcOpensOverTotal U)).symm

/-- `qcOpensOver_presenterIso` reduces the degree-zero square to `opensOver_compIso`. -/
theorem qcOpensOver_presenterIso_whisker :
    isoWhiskerRight (opensOver_compIso (a.app (op ⦋0⦌)))
        (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)) =
      (Functor.associator (opensOver X) (Over.pullback (a.app (op ⦋0⦌)))
          (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌))) ≪≫
        qcOpensOver_presenterIso a ≪≫
          Functor.associator (Opens.map (a.app (op ⦋0⦌)).hom)
            (DiagramOpens.fiber (forgetToTop.obj U) (op ⦋0⦌)) (qcOpensOverTotal U) ≪≫
          isoWhiskerLeft (Opens.map (a.app (op ⦋0⦌)).hom)
            (qcOpensOverTotal_comp_ofOpens U (op ⦋0⦌)) ≪≫
          (Functor.associator (Opens.map (a.app (op ⦋0⦌)).hom)
            (opensOver (U.obj (op ⦋0⦌))) (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌))).symm :=
  sorry

section
omit a U

/-- Degree-zero fiber inclusion of the constant simplicial space admits left Kan
extensions on type-valued presheaves. -/
instance fiber_constSpace_op_hasLeftKanExtension
    (P : (Opens (X.obj : Type u))ᵒᵖ ⥤ Type u) :
    (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).op.HasLeftKanExtension P :=
  sorry

/-- Degree-zero fiber inclusion of the constant simplicial space admits pointwise right
Kan extensions on type-valued presheaves. -/
instance fiber_constSpace_op_hasPointwiseRightKanExtension
    (P : (Opens (X.obj : Type u))ᵒᵖ ⥤ Type u) :
    (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Degree-zero inclusion of the constant simplicial space is continuous on the LC
underlying space. -/
instance fiber_constSpace_obj_isContinuous :
    (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)) :=
  constSpace_fiber_isContinuous X.obj (op ⦋0⦌)

/-- Degree-zero inclusion of the constant simplicial space is cocontinuous on the LC
underlying space. -/
instance fiber_constSpace_obj_isCocontinuous :
    (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).IsCocontinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)) :=
  constSpace_fiber_isCocontinuous X.obj (op ⦋0⦌)

/-- Degree-forgetting projection of the LC underlying space is continuous. -/
instance constProjection_obj_isContinuous :
    (constProjection X.obj).IsContinuous
      (zariskiTopology (constSpace X.obj)) (Opens.grothendieckTopology (X.obj : Type u)) :=
  constProjection_isContinuous X.obj

/-- Degree-forgetting projection of the LC underlying space is cocontinuous. -/
instance constProjection_obj_isCocontinuous :
    (constProjection X.obj).IsCocontinuous
      (zariskiTopology (constSpace X.obj)) (Opens.grothendieckTopology (X.obj : Type u)) :=
  constProjection_isCocontinuous X.obj

end

section
omit a

/-- Degree-zero inclusion `Grothendieck.ι` is continuous for the slice topologies. -/
instance grothendieck_ι_isContinuous :
    (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)).IsContinuous
      (qcTopology.over (U.obj (op ⦋0⦌))) (sliceTotalTopology qcTopology U) :=
  sorry

/-- Degree-zero inclusion `Grothendieck.ι` is cocontinuous for the slice topologies. -/
instance grothendieck_ι_isCocontinuous :
    (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)).IsCocontinuous
      (qcTopology.over (U.obj (op ⦋0⦌))) (sliceTotalTopology qcTopology U) :=
  sorry

/-- Degree-zero inclusion `Grothendieck.ι` admits left Kan extensions. -/
instance grothendieck_ι_op_hasLeftKanExtension
    (P : (Over (U.obj (op ⦋0⦌)))ᵒᵖ ⥤ Type u) :
    (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)).op.HasLeftKanExtension P :=
  sorry

/-- Degree-zero inclusion `Grothendieck.ι` admits pointwise right Kan extensions. -/
instance grothendieck_ι_op_hasPointwiseRightKanExtension
    (P : (Over (U.obj (op ⦋0⦌)))ᵒᵖ ⥤ Type u) :
    (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)).op.HasPointwiseRightKanExtension P :=
  sorry

end

/-- Degree-zero inclusion of opens of `U` into `U_Zar` is continuous. -/
instance fiber_forgetToTop_isContinuous (n : SimplexCategoryᵒᵖ) :
    (DiagramOpens.fiber (forgetToTop.obj U) n).IsContinuous
      (Opens.grothendieckTopology ((forgetToTop.obj U).obj n))
      (zariskiTopology (forgetToTop.obj U)) :=
  sorry

/-- Inverse image of opens along the degree-zero augmentation map is continuous. -/
instance opensMap_augmentation_isContinuous :
    (Opens.map (a.app (op ⦋0⦌)).hom).IsContinuous
      (Opens.grothendieckTopology X.obj)
      (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋0⦌))) :=
  sorry

/-- Stage inclusion followed by `qcOpensOverTotal` is continuous. -/
instance fiber_comp_qcOpensOverTotal_isContinuous :
    (DiagramOpens.fiber (forgetToTop.obj U) (op ⦋0⦌) ⋙ qcOpensOverTotal U).IsContinuous
      (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋0⦌)))
      (sliceTotalTopology qcTopology U) :=
  sorry

/-- The left presenting composite of `qcOpensOver_presenterIso` is continuous. -/
instance qcOpensOver_presenter_left_isContinuous :
    (opensOver X ⋙ sliceAugmentationPullback U a).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U) :=
  sorry

/-- The right presenting composite of `qcOpensOver_presenterIso` is continuous. -/
instance qcOpensOver_presenter_right_isContinuous :
    (qcOpensOver_zariskiTotalPresenter a).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U) :=
  sorry

/-- The composite `zariskiMap ⋙ qcOpensOverTotal` is continuous. -/
instance zariskiMap_comp_qcOpensOverTotal_isContinuous :
    (zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).IsContinuous
      (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U) :=
  sorry

/-- Left Kan extensions along `zariskiMap ⋙ qcOpensOverTotal`. -/
instance zariskiMap_comp_qcOpensOverTotal_op_hasLeftKanExtension
    (P : (zariskiSite (constSpace X.obj))ᵒᵖ ⥤ Type u) :
    (zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).op.HasLeftKanExtension P :=
  sorry

/-- The composite `fiber ⋙ zariskiMap ⋙ qcOpensOverTotal` is continuous. -/
instance fiber_const_comp_zariskiMap_qcOpensOverTotal_isContinuous :
    (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌) ⋙
        zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U) :=
  sorry

/-- Left Kan extensions along `fiber ⋙ zariskiMap ⋙ qcOpensOverTotal`. -/
instance fiber_const_comp_zariskiMap_qcOpensOverTotal_op_hasLeftKanExtension
    (P : (Opens X.obj)ᵒᵖ ⥤ Type u) :
    (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌) ⋙
        zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).op.HasLeftKanExtension P :=
  sorry

variable [HasWeakSheafify (qcTopology.over X) (Type u)]
variable [HasWeakSheafify (sliceTotalTopology qcTopology U) (Type u)]
variable [HasSheafify (sliceTotalTopology qcTopology U) (Type u)]
variable [HasWeakSheafify (zariskiTopology (forgetToTop.obj U)) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X.obj) (Type u)]
variable [HasSheafify (zariskiTopology (constSpace X.obj)) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋0⦌))) (Type u)]
variable [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u, (opensOver X).op.HasLeftKanExtension P]
variable [∀ P : (zariskiSite (forgetToTop.obj U))ᵒᵖ ⥤ Type u,
    (qcOpensOverTotal U).op.HasLeftKanExtension P]
variable [∀ P : (zariskiSite (constSpace X.obj))ᵒᵖ ⥤ Type u,
    (zariskiMap (toTopCatAugmentation a)).op.HasLeftKanExtension P]
variable [∀ F : (zariskiSite (constSpace X.obj))ᵒᵖ ⥤ Type u,
    (constProjection X.obj).op.HasPointwiseRightKanExtension F]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type u,
    (sliceForget U a).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type u,
    (sliceAugmentationPullback U a).op.HasLeftKanExtension P]
variable [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u,
    (Opens.map (a.app (op ⦋0⦌)).hom).op.HasLeftKanExtension P]
variable [∀ P : (Opens ((forgetToTop.obj U).obj (op ⦋0⦌)))ᵒᵖ ⥤ Type u,
    (DiagramOpens.fiber (forgetToTop.obj U) (op ⦋0⦌)).op.HasLeftKanExtension P]
variable [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u,
    (opensOver X ⋙ sliceAugmentationPullback U a).op.HasLeftKanExtension P]
variable [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u,
    (qcOpensOver_zariskiTotalPresenter a).op.HasLeftKanExtension P]

/-- Inverse image of `opensOverQcTopos` is sheaf pullback along `opensOver`. -/
def opensOverQcTopos_inverseImageIso :
    (opensOverQcTopos X)⁻¹ ≅
      (opensOver X).sheafPullback (Type u) (Opens.grothendieckTopology X.obj)
        (qcTopology.over X) :=
  Iso.refl _

/-- Inverse image of `qcOpensOverTotalTopos` is sheaf pullback along `qcOpensOverTotal`. -/
def qcOpensOverTotalTopos_inverseImageIso :
    (qcOpensOverTotalTopos U)⁻¹ ≅
      (qcOpensOverTotal U).sheafPullback (Type u) (zariskiTopology (forgetToTop.obj U))
        (sliceTotalTopology qcTopology U) :=
  Iso.refl _

/-- Inverse image of `sliceAugmentationTopos` is cocontinuous sheaf pullback along
`sliceForget`. -/
def sliceAugmentationTopos_inverseImageIso :
    (sliceAugmentationTopos qcTopology U a)⁻¹ ≅
      (sliceForget U a).sheafPullbackCocontinuous (Type u)
        (sliceTotalTopology qcTopology U) (qcTopology.over X) :=
  Iso.refl _

/-- Inverse image of `augmentationMorphism` is the composite of the constant-space
projection and `zariskiMap`. -/
def augmentationMorphism_inverseImageIso :
    (augmentationMorphism (toTopCatAugmentation a))⁻¹ ≅
      ((constProjection X.obj).morphismOfTopoiInOfCocontinuous
          (zariskiTopology (constSpace X.obj)) (Opens.grothendieckTopology X.obj))⁻¹ ⋙
        ((zariskiMap (toTopCatAugmentation a)).morphismOfTopoiInOfContinuous
          (zariskiTopology (constSpace X.obj)) (zariskiTopology (forgetToTop.obj U)))⁻¹ :=
  Iso.refl _

/-- Degree-zero continuous presenter square of `qcOpensOver_presenterIso`, as inverse
images of sheaf pullbacks. -/
def qcOpensOver_continuousInverseImage_comp :
    (opensOver X).sheafPullback (Type u) (Opens.grothendieckTopology X.obj)
        (qcTopology.over X) ⋙
      (sliceAugmentationPullback U a).sheafPullback (Type u) (qcTopology.over X)
        (sliceTotalTopology qcTopology U) ≅
      (qcOpensOver_zariskiTotalPresenter a).sheafPullback
        (Type u) (Opens.grothendieckTopology X.obj) (sliceTotalTopology qcTopology U) :=
  Adjunction.leftAdjointCompIso
    ((opensOver X).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology X.obj) (qcTopology.over X))
    ((sliceAugmentationPullback U a).sheafAdjunctionContinuous (Type u)
      (qcTopology.over X) (sliceTotalTopology qcTopology U))
    ((qcOpensOver_zariskiTotalPresenter a).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology X.obj) (sliceTotalTopology qcTopology U))
    (sheafPushforwardContinuousComp' (qcOpensOver_presenterIso a) (Type u)
      (Opens.grothendieckTopology X.obj) (qcTopology.over X)
      (sliceTotalTopology qcTopology U))


/-- `Over.map (a.app (op ⦋0⦌))` admits pointwise right Kan extensions. -/
instance sliceMap_op_hasPointwiseRightKanExtension
    (P : (Over (U.obj (op ⦋0⦌)))ᵒᵖ ⥤ Type u) :
    (Over.map (a.app (op ⦋0⦌))).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Degree-zero inclusion into `(LC_qc / U)_total` followed by `sliceForget` is
postcomposition with `a.app (op ⦋0⦌)`. -/
def grothendieck_ι_comp_sliceForget :
    Grothendieck.ι (sliceDiagram U) (op ⦋0⦌) ⋙ sliceForget U a ≅
      Over.map (a.app (op ⦋0⦌)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Inverse image along `zariskiMap` of the LC augmentation is sheaf pullback. -/
def zariskiMap_augmentation_inverseImageIso :
    ((zariskiMap (toTopCatAugmentation a)).morphismOfTopoiInOfContinuous
        (zariskiTopology (constSpace X.obj)) (zariskiTopology (forgetToTop.obj U)))⁻¹ ≅
      (zariskiMap (toTopCatAugmentation a)).sheafPullback (Type u)
        (zariskiTopology (constSpace X.obj)) (zariskiTopology (forgetToTop.obj U)) :=
  Iso.refl _

section
omit a U

/-- The degree-zero fiber inclusion is left adjoint to forget-degree on the constant
simplicial Zariski site. -/
def fiber_constProjectionAdj :
    DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌) ⊣ constProjection X.obj where
  unit := (fiber_comp_constProjection X.obj (op ⦋0⦌)).inv
  counit :=
    { app := fun V ↦
        (DiagramOpens.homMk (Opposite.op (SimplexCategory.isTerminalZero.from V.base.unop))
          fun _ hx ↦ hx :
          (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).obj
              ((constProjection X.obj).obj V) ⟶ V)
      naturality := sorry }
  left_triangle_components := sorry
  right_triangle_components := sorry

/-- Sites 7.27.3: continuous direct image of `constProjection` agrees with cocontinuous
direct image of the degree-zero fiber inclusion. -/
def constProjection_fiber_pushforwardIso
    [h_cont : (constProjection X.obj).IsContinuous
      (zariskiTopology (constSpace X.obj)) (Opens.grothendieckTopology (X.obj : Type u))]
    [h_coco : (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).IsCocontinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj))]
    [h_ran : ∀ P : (Opens (X.obj : Type u))ᵒᵖ ⥤ Type u,
      (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).op.HasPointwiseRightKanExtension P] :
    (constProjection X.obj).sheafPushforwardContinuous (Type u)
        (zariskiTopology (constSpace X.obj)) (Opens.grothendieckTopology (X.obj : Type u)) ≅
      (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).sheafPushforwardCocontinuous (Type u)
        (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)) :=
  @Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (Opens (X.obj : Type u)) inferInstance (zariskiSite (constSpace X.obj)) inferInstance
    (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj))
    (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)) (constProjection X.obj)
    (Type u) inferInstance fiber_constProjectionAdj h_cont h_coco h_ran

/-- Cocontinuous direct image of `constProjection` agrees with continuous direct image of
the degree-zero fiber inclusion, as right adjoints of `constProjection.op.ranAdjunction`
and of restriction along the fiber inclusion. -/
def constProjection_fiber_directImageIso :
    (constProjection X.obj).sheafPushforwardCocontinuous (Type u)
        (zariskiTopology (constSpace X.obj)) (Opens.grothendieckTopology (X.obj : Type u)) ≅
      (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)) :=
  NatIso.ofComponents
    (fun G ↦
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (X.obj : Type u)) (Type u)).preimageIso
        (NatIso.ofComponents
          (fun U ↦
            { hom :=
                ((constProjection X.obj).op.ranCounit.app G.obj).app
                  (op ((DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).obj U.unop))
              inv :=
                (((constProjection X.obj).op.ranAdjunction (Type u)).homEquiv
                    ((DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).op ⋙ G.obj)
                    G.obj
                  { app := fun V ↦
                      G.obj.map
                        (Quiver.Hom.op
                          (DiagramOpens.homMk
                              (Opposite.op (SimplexCategory.const ⦋0⦌ V.unop.base.unop 0))
                              fun _ hx ↦ hx :
                            V.unop ⟶
                              (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).obj
                                ((constProjection X.obj).obj V.unop)))
                    naturality := sorry }).app U
              hom_inv_id := sorry
              inv_hom_id := sorry })
          sorry))
    sorry

/-- Inverse image along the constant-space projection is sheaf pullback of the
degree-zero fiber inclusion, by matching direct images `constProjection_*_coco ≅ fiber_*_cont`. -/
def constProjection_fiberInverseImageIso :
    ((constProjection X.obj).morphismOfTopoiInOfCocontinuous
        (zariskiTopology (constSpace X.obj)) (Opens.grothendieckTopology (X.obj : Type u)))⁻¹ ≅
      (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).sheafPullback (Type u)
        (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)) :=
  Adjunction.leftAdjointUniq
    (((constProjection X.obj).sheafPullbackCocontinuousAdjunction
        (zariskiTopology (constSpace X.obj))
        (Opens.grothendieckTopology (X.obj : Type u))).ofNatIsoRight
      constProjection_fiber_directImageIso)
    ((DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)))

end

/-- Site-level identification of the two continuous presenters of `a⁻¹` through
degree zero. -/
def qcOpensOver_zariskiPresenterIso :
    DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌) ⋙ zariskiMap (toTopCatAugmentation a) ≅
      Opens.map (a.app (op ⦋0⦌)).hom ⋙ DiagramOpens.fiber (forgetToTop.obj U) (op ⦋0⦌) :=
  zariskiMap_fiber (toTopCatAugmentation a) (op ⦋0⦌)

/-- The degree-zero composite `fiber ⋙ zariskiMap ⋙ qcOpensOverTotal` is the named
presenter `qcOpensOver_zariskiTotalPresenter`. -/
def qcOpensOver_zariskiTotalPresenterIso :
    DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌) ⋙
        zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U ≅
      qcOpensOver_zariskiTotalPresenter a :=
  (Functor.associator
      (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌))
      (zariskiMap (toTopCatAugmentation a)) (qcOpensOverTotal U)).symm ≪≫
    isoWhiskerRight (qcOpensOver_zariskiPresenterIso a) (qcOpensOverTotal U) ≪≫
    Functor.associator
      (Opens.map (a.app (op ⦋0⦌)).hom)
      (DiagramOpens.fiber (forgetToTop.obj U) (op ⦋0⦌)) (qcOpensOverTotal U)

/-- Sheaf pullback along `zariskiMap` then `qcOpensOverTotal` is pullback along the
composite presenter. -/
def qcOpensOver_zariskiQcPullbackCompIso :
    (zariskiMap (toTopCatAugmentation a)).sheafPullback (Type u)
        (zariskiTopology (constSpace X.obj)) (zariskiTopology (forgetToTop.obj U)) ⋙
      (qcOpensOverTotal U).sheafPullback (Type u) (zariskiTopology (forgetToTop.obj U))
        (sliceTotalTopology qcTopology U) ≅
      (zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).sheafPullback
        (Type u) (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U) :=
  Adjunction.leftAdjointCompIso
    ((zariskiMap (toTopCatAugmentation a)).sheafAdjunctionContinuous (Type u)
      (zariskiTopology (constSpace X.obj)) (zariskiTopology (forgetToTop.obj U)))
    ((qcOpensOverTotal U).sheafAdjunctionContinuous (Type u)
      (zariskiTopology (forgetToTop.obj U)) (sliceTotalTopology qcTopology U))
    ((zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).sheafAdjunctionContinuous
      (Type u) (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U))
    (sheafPushforwardContinuousComp
      (zariskiMap (toTopCatAugmentation a)) (qcOpensOverTotal U) (Type u)
      (zariskiTopology (constSpace X.obj)) (zariskiTopology (forgetToTop.obj U))
      (sliceTotalTopology qcTopology U))

/-- Inverse image along `zariskiMap` then `h` is sheaf pullback of the composite
continuous presenter `zariskiMap ⋙ qcOpensOverTotal`. -/
def qcOpensOver_zariskiMap_qcOpensOverTotal_inverseImageIso :
    ((zariskiMap (toTopCatAugmentation a)).morphismOfTopoiInOfContinuous
        (zariskiTopology (constSpace X.obj)) (zariskiTopology (forgetToTop.obj U)))⁻¹ ⋙
      (qcOpensOverTotalTopos U)⁻¹ ≅
      (zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).sheafPullback
        (Type u) (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U) :=
  isoWhiskerRight (zariskiMap_augmentation_inverseImageIso a) ((qcOpensOverTotalTopos U)⁻¹) ≪≫
    isoWhiskerLeft
      ((zariskiMap (toTopCatAugmentation a)).sheafPullback (Type u)
        (zariskiTopology (constSpace X.obj)) (zariskiTopology (forgetToTop.obj U)))
      qcOpensOverTotalTopos_inverseImageIso ≪≫
    qcOpensOver_zariskiQcPullbackCompIso a

/-- Direct-image form of `qcOpensOver_zariskiTotalPresenterIso`: pushforward along the
composite `zariskiMap ⋙ qcOpensOverTotal` then the degree-zero fiber is pushforward
along the named presenter. -/
def qcOpensOver_fiberPresenterPushforwardIso
    [h_fiber : (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj))]
    [h_comp : (zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).IsContinuous
      (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U)]
    [h_compFG : (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌) ⋙
        zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U)]
    [h_presenter : (qcOpensOver_zariskiTotalPresenter a).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U)] :
    (zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).sheafPushforwardContinuous
        (Type u) (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U) ⋙
      (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)) ≅
      (qcOpensOver_zariskiTotalPresenter a).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U) :=
  NatIso.ofComponents
    (fun M ↦
      { hom := ⟨whiskerRight (NatTrans.op (qcOpensOver_zariskiTotalPresenterIso a).inv) M.obj⟩
        inv := ⟨whiskerRight (NatTrans.op (qcOpensOver_zariskiTotalPresenterIso a).hom) M.obj⟩
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Sheaf pullback along the degree-zero fiber then the composite `zariskiMap ⋙
qcOpensOverTotal` is pullback along the named presenter. -/
def qcOpensOver_fiberPresenterPullbackIso
    [h_fiber : (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj))]
    [h_comp : (zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).IsContinuous
      (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U)]
    [h_compFG : (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌) ⋙
        zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U)]
    [h_presenter : (qcOpensOver_zariskiTotalPresenter a).IsContinuous
      (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U)] :
    (DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).sheafPullback (Type u)
        (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)) ⋙
      (zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).sheafPullback
        (Type u) (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U) ≅
      (qcOpensOver_zariskiTotalPresenter a).sheafPullback
        (Type u) (Opens.grothendieckTopology (X.obj : Type u))
        (sliceTotalTopology qcTopology U) :=
  Adjunction.leftAdjointCompIso
    ((DiagramOpens.fiber (constSpace X.obj) (op ⦋0⦌)).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology (X.obj : Type u)) (zariskiTopology (constSpace X.obj)))
    ((zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).sheafAdjunctionContinuous
      (Type u) (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U))
    ((qcOpensOver_zariskiTotalPresenter a).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology (X.obj : Type u)) (sliceTotalTopology qcTopology U))
    (qcOpensOver_fiberPresenterPushforwardIso a)

/-- `a⁻¹ ⋙ h⁻¹` is sheaf pullback along the degree-zero continuous presenter
`qcOpensOver_zariskiTotalPresenter`. -/
def qcOpensOver_augmentationInverseImage_iso :
    (augmentationMorphism (toTopCatAugmentation a))⁻¹ ⋙ (qcOpensOverTotalTopos U)⁻¹ ≅
      (qcOpensOver_zariskiTotalPresenter a).sheafPullback
        (Type u) (Opens.grothendieckTopology X.obj) (sliceTotalTopology qcTopology U) :=
  isoWhiskerRight (augmentationMorphism_inverseImageIso a) ((qcOpensOverTotalTopos U)⁻¹) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft
        (((constProjection X.obj).morphismOfTopoiInOfCocontinuous
            (zariskiTopology (constSpace X.obj))
            (Opens.grothendieckTopology (X.obj : Type u)))⁻¹)
      (qcOpensOver_zariskiMap_qcOpensOverTotal_inverseImageIso a) ≪≫
    isoWhiskerRight constProjection_fiberInverseImageIso
      ((zariskiMap (toTopCatAugmentation a) ⋙ qcOpensOverTotal U).sheafPullback
        (Type u) (zariskiTopology (constSpace X.obj)) (sliceTotalTopology qcTopology U)) ≪≫
    (qcOpensOver_fiberPresenterPullbackIso a)

/-- Hom-equivalence presenting `sliceForget ⊣ sliceAugmentationPullback` on a morphism
`Over.map (a.app n) Y.fiber ⟶ V`. -/
def sliceForgetHomEquiv
    (Y : sliceTotalSite U) (V : Over X) :
    ((sliceForget U a).obj Y ⟶ V) ≃ (Y ⟶ (sliceAugmentationPullback U a).obj V) where
  toFun f :=
    { base := (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op
      fiber :=
        ((Over.mapPullbackAdj (a.app (op ⦋0⦌))).homEquiv
            ((Over.map (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op)).obj Y.fiber) V)
          (((Over.mapComp (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op)
                (a.app (op ⦋0⦌))).hom.app Y.fiber) ≫
            ((Over.mapCongr (a.app Y.base)
                  (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫ a.app (op ⦋0⦌))
                  ((a.naturality (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op).trans
                      (Category.comp_id (a.app Y.base))).symm).inv.app Y.fiber ≫
              f)) }
  invFun g :=
    ((Over.mapCongr (a.app Y.base)
          (U.map g.base ≫ a.app (op ⦋0⦌))
          ((a.naturality g.base).trans (Category.comp_id (a.app Y.base))).symm).hom.app Y.fiber) ≫
      ((Over.mapComp (U.map g.base) (a.app (op ⦋0⦌))).hom.app Y.fiber) ≫
        ((Over.mapPullbackAdj (a.app (op ⦋0⦌))).homEquiv
            ((Over.map (U.map g.base)).obj Y.fiber) V).symm g.fiber
  left_inv := sorry
  right_inv := sorry

/-- Case A: `sliceForget` is left adjoint to the continuous presenter
`sliceAugmentationPullback`. -/
def sliceForgetAdj :
    sliceForget U a ⊣ sliceAugmentationPullback U a :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Y V ↦ sliceForgetHomEquiv a Y V
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Direct images of the Case A continuous presenter and of `sliceForget` agree,
by Sites Lemma 7.27.3 on `sliceForget ⊣ sliceAugmentationPullback`. -/
def sliceAugmentation_pushforward_iso :
    (sliceAugmentationPullback U a).sheafPushforwardContinuous (Type u)
        (qcTopology.over X) (sliceTotalTopology qcTopology U) ≅
      (sliceForget U a).sheafPushforwardCocontinuous (Type u)
        (sliceTotalTopology qcTopology U) (qcTopology.over X) :=
  Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (sliceForget U a) (sliceAugmentationPullback U a) (Type u) (sliceForgetAdj a)

/-- Inverse image of `a_qc` is sheaf pullback along the Case A continuous presenter. -/
def sliceAugmentationTopos_continuousInverseImage :
    (sliceAugmentationTopos qcTopology U a)⁻¹ ≅
      (sliceAugmentationPullback U a).sheafPullback (Type u)
        (qcTopology.over X) (sliceTotalTopology qcTopology U) :=
  Adjunction.leftAdjointUniq
    ((sliceForget U a).sheafPullbackCocontinuousAdjunction
      (sliceTotalTopology qcTopology U) (qcTopology.over X))
    (((sliceAugmentationPullback U a).sheafAdjunctionContinuous (Type u)
        (qcTopology.over X) (sliceTotalTopology qcTopology U)).ofNatIsoRight
      (sliceAugmentation_pushforward_iso a))

/-- Inverse-image form of `a ∘ h = h₋₁ ∘ a_qc` as morphisms of topoi
`Sh((LC_qc / U)_total) ⟶ Sh(X)`. The four arrows are `h = qcOpensOverTotalTopos`,
`a = augmentationMorphism (toTopCatAugmentation a)`, `h₋₁ = opensOverQcTopos`,
and `a_qc = sliceAugmentationTopos qcTopology`. -/
def qcOpensOver_inverseImage_comp :
    (augmentationMorphism (toTopCatAugmentation a))⁻¹ ⋙ (qcOpensOverTotalTopos U)⁻¹ ≅
      (opensOverQcTopos X)⁻¹ ⋙ (sliceAugmentationTopos qcTopology U a)⁻¹ :=
  qcOpensOver_augmentationInverseImage_iso a ≪≫
    (qcOpensOver_continuousInverseImage_comp a).symm ≪≫
    isoWhiskerLeft ((opensOver X).sheafPullback (Type u)
        (Opens.grothendieckTopology X.obj) (qcTopology.over X))
      (sliceAugmentationTopos_continuousInverseImage a).symm ≪≫
    isoWhiskerRight
      (opensOverQcTopos_inverseImageIso.symm)
      ((sliceAugmentationTopos qcTopology U a)⁻¹)

/-- Restriction of `a⁻¹` to degree zero is inverse image along the degree-zero map. -/
def qcOpensOver_inverseImage_comp_augmentation :
    (augmentationMorphism (toTopCatAugmentation a))⁻¹ ⋙
        sheafComponent (forgetToTop.obj U) 0 (Type u) ≅
      (componentTopos (toTopCatAugmentation a) 0)⁻¹ :=
  inverseImage_sheafComponent (toTopCatAugmentation a) 0

end LCCat
