module

public import Mathlib.CategoryTheory.Functor.Const
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Simplicial.Slice
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationTopos

/-! # Augmentations of simplicial slice sites -/

set_option backward.privateInPublic true

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped Simplicial

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Postcomposition along the augmentation components defines arrows on the total slice category. -/
private def sliceForgetMap {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
    {Y Z : sliceTotalSite U} (f : Y ⟶ Z) :
    (Over.map (a.app Y.base)).obj Y.fiber ⟶
      (Over.map (a.app Z.base)).obj Z.fiber :=
    ((Over.mapCongr (a.app Y.base) (U.map f.base ≫ a.app Z.base)
          ((Category.comp_id (a.app Y.base)).symm.trans (a.naturality f.base).symm)).hom ≫
        (Over.mapComp (U.map f.base) (a.app Z.base)).hom).app Y.fiber ≫
      (Over.map (a.app Z.base)).map f.fiber

/-- The augmentation arrow maps preserve identities and composition. -/
private theorem sliceForget_laws {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (∀ Y : sliceTotalSite U, sliceForgetMap U a (Y := Y) (Z := Y) (𝟙 Y) = 𝟙 _) ∧
    (∀ {Y Z W : sliceTotalSite U} (f : Y ⟶ Z) (g : Z ⟶ W),
      sliceForgetMap U a (Y := Y) (Z := W) (f ≫ g) = sliceForgetMap U a (Y := Y) (Z := Z) f ≫ sliceForgetMap U a (Y := Z) (Z := W) g) := by
  sorry

/-- The augmentation induces postcomposition on the total slice category. -/
def sliceForget {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) : sliceTotalSite U ⥤ Over X where
  obj Y := (Over.map (a.app Y.base)).obj Y.fiber
  map {Y Z} f := sliceForgetMap U a (Y := Y) (Z := Z) f
  map_id := (sliceForget_laws U a).1
  map_comp := (sliceForget_laws U a).2

/-- On objects, `sliceForget a` is postcomposition with the component `a.app n`. -/
theorem sliceForget_obj {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (Y : sliceTotalSite U) :
    (sliceForget U a).obj Y = (Over.map (a.app Y.base)).obj Y.fiber :=
  rfl

/-- Postcomposition through degree zero defines arrows on the total slice category. -/
private def sliceForget_ofAugmentationMap {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
    {Y Z : sliceTotalSite U} (f : Y ⟶ Z) :
    (Over.map (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫ a.app (op ⦋0⦌))).obj Y.fiber ⟶
      (Over.map (U.map (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op ≫ a.app (op ⦋0⦌))).obj Z.fiber :=
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

/-- The augmentation arrow maps preserve identities and composition. -/
private theorem sliceForget_ofAugmentation_laws {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (∀ Y : sliceTotalSite U, sliceForget_ofAugmentationMap U a (Y := Y) (Z := Y) (𝟙 Y) = 𝟙 _) ∧
    (∀ {Y Z W : sliceTotalSite U} (f : Y ⟶ Z) (g : Z ⟶ W),
      sliceForget_ofAugmentationMap U a (Y := Y) (Z := W) (f ≫ g) = sliceForget_ofAugmentationMap U a (Y := Y) (Z := Z) f ≫ sliceForget_ofAugmentationMap U a (Y := Z) (Z := W) g) := by
  sorry

/-- The augmentation induces postcomposition on the total slice category. -/
def sliceForget_ofAugmentation {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) : sliceTotalSite U ⥤ Over X where
  obj Y := (Over.map
        (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫ a.app (op ⦋0⦌))).obj
      Y.fiber
  map {Y Z} f := sliceForget_ofAugmentationMap U a (Y := Y) (Z := Z) f
  map_id := (sliceForget_ofAugmentation_laws U a).1
  map_comp := (sliceForget_ofAugmentation_laws U a).2

/-- On objects, `sliceForget_ofAugmentation` is the common composite through degree zero. -/
theorem sliceForget_ofAugmentation_obj {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (Y : sliceTotalSite U) :
    (sliceForget_ofAugmentation U a).obj Y =
      (Over.map
          (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫
            a.app (op ⦋0⦌))).obj Y.fiber :=
  rfl

/-- Naturality of the augmentation identifies postcomposition with its degree-zero composite. -/
private def sliceForgetAugmentationComponent {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (Y : sliceTotalSite U) :
    (sliceForget U a).obj Y ≅ (sliceForget_ofAugmentation U a).obj Y :=
  (Over.mapCongr (a.app Y.base)
          (U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op ≫ a.app (op ⦋0⦌))
          ((a.naturality (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op).trans
            (Category.comp_id (a.app Y.base))).symm).app Y.fiber

/-- The canonical postcomposition comparisons commute with arrows of the total category. -/
private theorem sliceForget_iso_ofAugmentation_naturality {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
    {Y Z : sliceTotalSite U} (f : Y ⟶ Z) :
    (sliceForget U a).map f ≫ (sliceForgetAugmentationComponent U a Z).hom =
      (sliceForgetAugmentationComponent U a Y).hom ≫ (sliceForget_ofAugmentation U a).map f := by
  sorry

/-- Postcomposition along an augmentation is naturally isomorphic to its degree-zero presentation. -/
def sliceForget_iso_ofAugmentation {X : C} (U : SimplicialObject C)
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    sliceForget U a ≅ sliceForget_ofAugmentation U a :=
  NatIso.ofComponents (sliceForgetAugmentationComponent U a)
    (fun f ↦ sliceForget_iso_ofAugmentation_naturality U a f)

/-- A Grothendieck topology is generated by its covering presieves. -/
private theorem sliceGeneratedTopology_eq {D : Type*} [Category D]
    (K : GrothendieckTopology D) : K.toPrecoverage.toGrothendieck = K := by
  apply le_antisymm K.toGrothendieck_toPrecoverage_le
  intro V R hR
  have h : R.arrows ∈ K.toPrecoverage V := by
    change Sieve.generate R.arrows ∈ K V
    simpa using hR
  simpa using (Precoverage.generate_mem_toGrothendieck h)

/-- Passing to the topology generated by covering presieves leaves the category of sheaves unchanged. -/
private def sliceTopologySheafEquiv {D : Type*} [Category D]
    (K : GrothendieckTopology D) :
    Sheaf K (Type w) ≌ Sheaf K.toPrecoverage.toGrothendieck (Type w) :=
  Equivalence.mk
    { obj := fun G ↦ ⟨G.obj, by simpa only [sliceGeneratedTopology_eq K] using G.property⟩
      map := fun α ↦ ObjectProperty.homMk α.hom }
    { obj := fun G ↦ ⟨G.obj, by simpa only [sliceGeneratedTopology_eq K] using G.property⟩
      map := fun α ↦ ObjectProperty.homMk α.hom }
    (NatIso.ofComponents (fun G ↦
      { hom := ObjectProperty.homMk (𝟙 G.obj)
        inv := ObjectProperty.homMk (𝟙 G.obj) }))
    (NatIso.ofComponents (fun G ↦
      { hom := ObjectProperty.homMk (𝟙 G.obj)
        inv := ObjectProperty.homMk (𝟙 G.obj) }))

/-- The identity on presheaves transports the sheaf topos to its generated-topology presentation. -/
private def sliceTopologyTransportTopos {D : Type*} [Category D]
    (K : GrothendieckTopology D) : MorphismOfTopoiIn K K.toPrecoverage.toGrothendieck where
  inverseImageFunctor := LeftExactFunctor.of (sliceTopologySheafEquiv K).functor
  pushforward := (sliceTopologySheafEquiv K).inverse
  adjunction := (sliceTopologySheafEquiv K).toAdjunction

variable (J : GrothendieckTopology C)
variable {X : C} (U : SimplicialObject C)
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
variable [HasPullbacks C]

/-- Up to the canonical adjunction comparison, the composites of `Over.pullback (a.app (op ⦋0⦌))`
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
  rfl

/-- The degree-zero pullback inclusion functor `C / X ⥤ (C / U)_total`, sending `V / X`
to the degree-zero object `V ×_X U_0 / U_0`. -/
def sliceAugmentationPullback : Over X ⥤ sliceTotalSite U :=
  Over.pullback (a.app (op ⦋0⦌)) ⋙ Grothendieck.ι (sliceDiagram U) (op ⦋0⦌)

/-- On objects, `sliceAugmentationPullback` is fibre product with `U_0`, included in
degree zero. -/
theorem sliceAugmentationPullback_obj (V : Over X) :
    (sliceAugmentationPullback U a).obj V =
      ⟨op ⦋0⦌, (Over.pullback (a.app (op ⦋0⦌))).obj V⟩ :=
  rfl

/-- The degree-zero pullback inclusion functor `sliceAugmentationPullback` is continuous for the
total topology. -/
private theorem sliceAugmentationPullback_continuous :
    (sliceAugmentationPullback U a).IsContinuous (J.over X) (sliceTotalTopology J U) := by
  have hι := Grothendieck.HasSheafTransitions.component_continuous
    (F := sliceDiagram U) (J := slicePrecoverage J U) ⦋0⦌
  rw [show (slicePrecoverage J U (op ⦋0⦌)).toGrothendieck =
    J.over (U.obj (op ⦋0⦌)) from sliceGeneratedTopology_eq _] at hι
  exact @Functor.isContinuous_comp _ _ _ _ _ _
    (Over.pullback (a.app (op ⦋0⦌))) (Grothendieck.ι (sliceDiagram U) (op ⦋0⦌))
    (J.over X) (J.over (U.obj (op ⦋0⦌))) (sliceTotalTopology J U) (J.overPullback_isContinuous _) hι

/-- The degree-zero pullback inclusion is continuous for the total slice topology. -/
instance sliceAugmentationPullback_isContinuous :
    (sliceAugmentationPullback U a).IsContinuous (J.over X) (sliceTotalTopology J U) :=
  sliceAugmentationPullback_continuous J U a

/-- The localization `a0 : C / U_0 ⥤ C / X` is an augmentation of the slice diagram in the
cocontinuous presentation of the simplicial slice sites. -/
theorem sliceDiagram_isAugmentation :
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

/-- The total postcomposition functor is continuous for the total and slice topologies. -/
instance sliceForget_isContinuous :
    (sliceForget U a).IsContinuous (sliceTotalTopology J U) (J.over X) := by
  sorry


section PostcompositionTopos

variable [HasSheafify (sliceTotalTopology J U) (Type w)]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type w,
  (sliceForget U a).op.HasPointwiseRightKanExtension P]

/-- The total augmentation topos morphism presented by postcomposition along the augmentation. -/
def sliceAugmentationTopos : MorphismOfTopoiIn (J.over X) (sliceTotalTopology J U) :=
  (sliceForget U a).morphismOfTopoiInOfCocontinuous (sliceTotalTopology J U) (J.over X)

omit [HasPullbacks C] in
/-- The inverse image of the postcomposition presentation is its sheafified restriction. -/
theorem sliceAugmentationTopos_inverseImage :
    (sliceAugmentationTopos J U a).inverseImage =
      (sliceForget U a).sheafPullbackCocontinuous (Type w)
        (sliceTotalTopology J U) (J.over X) := rfl

end PostcompositionTopos

variable [HasSheafify (sliceTotalTopology J U) (Type (max u v w))]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type (max u v w),
  (sliceForget U a).op.HasPointwiseRightKanExtension P]

variable [HasSheafify (J.over X).toPrecoverage.toGrothendieck (Type (max u v w))]
variable [∀ n, HasSheafify (slicePrecoverage J U n).toGrothendieck (Type (max u v w))]
variable [∀ (n : SimplexCategory) (P : (Over (U.obj (op n)))ᵒᵖ ⥤ Type (max u v w)),
  (Grothendieck.IsAugmentation.stageFunctor (sliceDiagram U)
    (Over.map (a.app (op ⦋0⦌))) n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n)
  (P : (Over (U.obj (op n)))ᵒᵖ ⥤ Type (max u v w)),
  (Over.map (U.map φ.op)).op.HasPointwiseRightKanExtension P]

/-- The augmentation of slice sites induces the generic total augmentation morphism of topoi,
transported from the generated topology on the target slice. -/
def sliceAugmentationTopos_ofAugmentation :
    MorphismOfTopoiIn (J.over X) (sliceTotalTopology J U) :=
  MorphismOfTopoiIn.comp (sliceTopologyTransportTopos (J.over X))
    (@Grothendieck.IsAugmentation.totalTopos (sliceDiagram U) (slicePrecoverage J U)
      (CategoryTheory.Over X) inferInstance (J.over X).toPrecoverage
      (Over.map (a.app (op ⦋0⦌)))
      (J.over_toPrecoverage_isSite X) (fun n ↦ J.over_toPrecoverage_isSite (U.obj n))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance (sliceDiagram_isFiberwiseSite J U) (sliceDiagram_isAugmentation J U a))

/-- The common degree-zero composite is canonically isomorphic to postcomposition
along the augmentation component in every degree. -/
private def sliceStageAugmentationIso (n : SimplexCategory) :
    Grothendieck.IsAugmentation.stageFunctor (sliceDiagram U)
        (Over.map (a.app (op ⦋0⦌))) n ≅ Over.map (a.app (op n)) :=
  (Over.mapComp (U.map (SimplexCategory.const ⦋0⦌ n 0).op)
      (a.app (op ⦋0⦌))).symm ≪≫
    Over.mapCongr _ _ ((a.naturality (SimplexCategory.const ⦋0⦌ n 0).op).trans
      (Category.comp_id (a.app (op n))))

/-- Common degree-zero postcomposition is continuous for the generated slice topologies. -/
private theorem sliceStageAugmentation_isContinuous (n : SimplexCategory) :
    (Grothendieck.IsAugmentation.stageFunctor (sliceDiagram U)
      (Over.map (a.app (op ⦋0⦌))) n).IsContinuous
      (slicePrecoverage J U (op n)).toGrothendieck
      (J.over X).toPrecoverage.toGrothendieck := by
  change (Over.map (U.map (SimplexCategory.const ⦋0⦌ n 0).op) ⋙
    Over.map (a.app (op ⦋0⦌))).IsContinuous _ _
  rw [show (slicePrecoverage J U (op n)).toGrothendieck = J.over (U.obj (op n)) from
    sliceGeneratedTopology_eq _, sliceGeneratedTopology_eq]
  exact @Functor.isContinuous_comp _ _ _ _ _ _
    (Over.map (U.map (SimplexCategory.const ⦋0⦌ n 0).op))
    (Over.map (a.app (op ⦋0⦌))) (J.over (U.obj (op n)))
    (J.over (U.obj (op ⦋0⦌))) (J.over X)
    (Functor.isContinuous_of_coverPreserving
      (GrothendieckTopology.over_map_compatiblePreserving J _)
      (GrothendieckTopology.over_map_coverPreserving J _))
    (Functor.isContinuous_of_coverPreserving
      (GrothendieckTopology.over_map_compatiblePreserving J _)
      (GrothendieckTopology.over_map_coverPreserving J _))

/-- The generic augmentation construction makes each common-composite stage functor cocontinuous. -/
private theorem sliceStageAugmentation_isCocontinuous (n : SimplexCategory) :
    (Grothendieck.IsAugmentation.stageFunctor (sliceDiagram U)
      (Over.map (a.app (op ⦋0⦌))) n).IsCocontinuous
      (slicePrecoverage J U (op n)).toGrothendieck
      (J.over X).toPrecoverage.toGrothendieck :=
  Grothendieck.IsAugmentation.stageFunctor_isCocontinuous
    (sliceDiagram U) (slicePrecoverage J U) (J.over X).toPrecoverage
    (Over.map (a.app (op ⦋0⦌))) n

/-- The stage inverse image is canonically the continuous restriction along its presenting functor. -/
private def sliceStageInverseImageIso (n : SimplexCategory) :=
  @Functor.CocontinuousPullback.comparisonIso _ _ _ _
    (Grothendieck.IsAugmentation.stageFunctor (sliceDiagram U)
      (Over.map (a.app (op ⦋0⦌))) n)
    (slicePrecoverage J U (op n)).toGrothendieck (J.over X).toPrecoverage.toGrothendieck
    inferInstance inferInstance
    (sliceStageAugmentation_isContinuous J U a n)
    (sliceStageAugmentation_isCocontinuous J U a n) inferInstance

/-- On each total object, restriction along the augmentation identifies with the
corresponding stage inverse image through the canonical sheafification comparison. -/
private def sliceAugmentationSectionIso (G : Sheaf (J.over X) (Type (max u v w)))
    (Y : (sliceTotalSite U)ᵒᵖ) :
    (((sliceForget U a).sheafPushforwardContinuous (Type (max u v w))
      (sliceTotalTopology J U) (J.over X)).obj G).obj.obj Y ≅
    ((sliceAugmentationTopos_ofAugmentation J U a).inverseImage.obj G).obj.obj Y :=
  G.obj.mapIso ((sliceStageAugmentationIso U a Y.unop.base.unop).app Y.unop.fiber).op ≪≫
    ((evaluation (Over (U.obj Y.unop.base))ᵒᵖ (Type (max u v w))).obj (op Y.unop.fiber)).mapIso
      ((sheafToPresheaf (slicePrecoverage J U Y.unop.base).toGrothendieck (Type (max u v w))).mapIso
        (((sliceStageInverseImageIso J U a Y.unop.base.unop).app
          ((sliceTopologySheafEquiv (J.over X)).functor.obj G)).symm))

/-- The sectionwise augmentation comparisons commute with total restriction maps
in both directions and with morphisms of input sheaves. -/
private theorem sliceAugmentation_inverseImageIso_laws :
    (∀ (G : Sheaf (J.over X) (Type (max u v w))) {Y Z : (sliceTotalSite U)ᵒᵖ} (f : Y ⟶ Z),
      (((sliceForget U a).sheafPushforwardContinuous (Type (max u v w))
        (sliceTotalTopology J U) (J.over X)).obj G).obj.map f ≫
          (sliceAugmentationSectionIso J U a G Z).hom =
        (sliceAugmentationSectionIso J U a G Y).hom ≫
          ((sliceAugmentationTopos_ofAugmentation J U a).inverseImage.obj G).obj.map f) ∧
    (∀ (G : Sheaf (J.over X) (Type (max u v w))) {Y Z : (sliceTotalSite U)ᵒᵖ} (f : Y ⟶ Z),
      ((sliceAugmentationTopos_ofAugmentation J U a).inverseImage.obj G).obj.map f ≫
          (sliceAugmentationSectionIso J U a G Z).inv =
        (sliceAugmentationSectionIso J U a G Y).inv ≫
          (((sliceForget U a).sheafPushforwardContinuous (Type (max u v w))
            (sliceTotalTopology J U) (J.over X)).obj G).obj.map f) ∧
    (∀ {G H : Sheaf (J.over X) (Type (max u v w))} (α : G ⟶ H) (Y : (sliceTotalSite U)ᵒᵖ),
      (((sliceForget U a).sheafPushforwardContinuous (Type (max u v w))
        (sliceTotalTopology J U) (J.over X)).map α).hom.app Y ≫
          (sliceAugmentationSectionIso J U a H Y).hom =
        (sliceAugmentationSectionIso J U a G Y).hom ≫
          ((sliceAugmentationTopos_ofAugmentation J U a).inverseImage.map α).hom.app Y) := by
  sorry

/-- The postcomposition inverse image is canonically isomorphic to the
assembled inverse image of the augmentation of the slice sites. -/
def sliceAugmentation_inverseImageIso :
    (sliceAugmentationTopos J U a).inverseImage ≅
      (sliceAugmentationTopos_ofAugmentation J U a).inverseImage :=
  Functor.CocontinuousPullback.comparisonIso (sliceForget U a)
      (sliceTotalTopology J U) (J.over X) ≪≫
    NatIso.ofComponents
      (fun G ↦
        { hom := ObjectProperty.homMk
            { app := fun Y ↦ (sliceAugmentationSectionIso J U a G Y).hom
              naturality := fun _ _ f ↦ (sliceAugmentation_inverseImageIso_laws J U a).1 G f }
          inv := ObjectProperty.homMk
            { app := fun Y ↦ (sliceAugmentationSectionIso J U a G Y).inv
              naturality := fun _ _ f ↦ (sliceAugmentation_inverseImageIso_laws J U a).2.1 G f }
          hom_inv_id := by
            ext Y x
            exact congrArg (fun f ↦ f x) ((sliceAugmentationSectionIso J U a G Y).hom_inv_id)
          inv_hom_id := by
            ext Y x
            exact congrArg (fun f ↦ f x) ((sliceAugmentationSectionIso J U a G Y).inv_hom_id) })
      (fun α ↦ by
        ext Y x
        exact congrArg (fun f ↦ f x) ((sliceAugmentation_inverseImageIso_laws J U a).2.2 α Y))

/-- The direct images of the two canonical total augmentation presentations agree
by the mate of their inverse-image comparison. -/
def sliceAugmentation_pushforwardIso :
    (sliceAugmentationTopos J U a).pushforward ≅
      (sliceAugmentationTopos_ofAugmentation J U a).pushforward :=
  MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
    (sliceAugmentationTopos J U a) (sliceAugmentationTopos_ofAugmentation J U a)
    (sliceAugmentation_inverseImageIso J U a)

end CategoryTheory.SimplicialObject
