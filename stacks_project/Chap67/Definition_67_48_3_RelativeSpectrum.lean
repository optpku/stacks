module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_6_7
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Relative spectrum of a quasi-coherent algebra on an algebraic space

The relative spectrum `relativeSpec A` of a quasi-coherent `𝒪_X`-algebra is the algebraic space
over `S` whose `T`-points are morphisms `T ⟶ X` together with a morphism of `𝒪_X`-algebras
`A ⟶ g_* 𝒪_T`. Algebra maps are recorded on the Type `u` Zariski site of an étale atlas of `X`,
subject to descent along the two projections of an atlas of `U ×_X U`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Functor CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The `𝒪_X`-algebra `g_* 𝒪_T` associated to a test morphism `g : ofOver T ⟶ X`. -/
def relativeSpectrumTarget {X : AlgebraicSpace S} {T : Over S} (g : ofOver T ⟶ X) :
    Under (commRingStructureSheaf X) :=
  Under.mk (commRingStructureSheafMap g)

/-- The comparison `T ×_Y W ⟶ X ×_Y W` induced by `t : ofOver T ⟶ X`. -/
def etaleBaseChangeMapOfPrecomp {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeSpace (t ≫ f) W ⟶ etaleBaseChangeSpace f W :=
  pullback.map (homFunctor (t ≫ f)) (homFunctor W.hom) (homFunctor f) (homFunctor W.hom)
    t (𝟙 _) (𝟙 _) sorry sorry

/-- After composing with the first projection, `etaleBaseChangeMapOfPrecomp t f W` recovers
`t` on the `T`-factor. -/
theorem etaleBaseChangeMapOfPrecomp_comp_fst {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeMapOfPrecomp t f W ≫ etaleBaseChangeHom f W =
      etaleBaseChangeHom (t ≫ f) W ≫ t :=
  sorry

/-- The pullback-associator `T ×_Y W ⟶ T ×_X (X ×_Y W)` as a morphism of algebraic spaces. -/
def etaleBaseChangeAssocHom {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeSpace (t ≫ f) W ⟶ pullback (etaleBaseChangeHom f W) t :=
  pullback.lift (etaleBaseChangeMapOfPrecomp t f W) (etaleBaseChangeHom (t ≫ f) W) sorry

/-- The associator projects to `T ×_Y W ⟶ X ×_Y W` along `pullback.fst`. -/
theorem etaleBaseChangeAssocHom_fst {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeAssocHom t f W ≫ pullback.fst (etaleBaseChangeHom f W) t =
      etaleBaseChangeMapOfPrecomp t f W :=
  sorry

/-- The associator `T ×_Y W ⟶ T ×_X (X ×_Y W)` in the spaces étale site of `ofOver T`. -/
def etaleBaseChangeAssoc {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeObj (t ≫ f) W ⟶
      (spacesEtalePullback t).obj (etaleBaseChangeObj f W) :=
  MorphismProperty.Over.homMk (etaleBaseChangeAssocHom t f W) sorry

/-- The underlying algebraic-space morphism of `etaleBaseChangeAssoc` is
`etaleBaseChangeAssocHom`. -/
theorem etaleBaseChangeAssoc_left {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    (etaleBaseChangeAssoc t f W).left = etaleBaseChangeAssocHom t f W :=
  rfl

/-- The inverse associator `T ×_X (X ×_Y W) ⟶ T ×_Y W` as a morphism of algebraic spaces. -/
def etaleBaseChangeAssocInvHom {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    pullback (etaleBaseChangeHom f W) t ⟶ etaleBaseChangeSpace (t ≫ f) W :=
  (CategoryTheory.Limits.pullback.lift
      (pullback.snd (etaleBaseChangeHom f W) t)
      (pullback.fst (etaleBaseChangeHom f W) t ≫ etaleBaseChangeSnd f W) sorry :
    (pullback (etaleBaseChangeHom f W) t).functorOfPoints ⟶
      (etaleBaseChangeSpace (t ≫ f) W).functorOfPoints)

/-- The inverse associator in the spaces étale site of `ofOver T`. -/
def etaleBaseChangeAssocInv {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    (spacesEtalePullback t).obj (etaleBaseChangeObj f W) ⟶ etaleBaseChangeObj (t ≫ f) W :=
  MorphismProperty.Over.homMk (etaleBaseChangeAssocInvHom t f W) sorry

/-- The underlying algebraic-space morphism of `etaleBaseChangeAssocInv` is
`etaleBaseChangeAssocInvHom`. -/
theorem etaleBaseChangeAssocInv_left {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    (etaleBaseChangeAssocInv t f W).left = etaleBaseChangeAssocInvHom t f W :=
  rfl

/-- Comparison of the functor-of-points fibre product `T ×_X V` with the categorical fibre
product used by `spacesEtalePullback`. -/
def etaleBaseChangeToSpacesPullback {X : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (V : smallEtaleSite X) :
    etaleBaseChangeObj t V ⟶
      (spacesEtalePullback t).obj ((smallEtaleInclusion X).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (etaleBaseChangeSnd t V) (etaleBaseChangeHom t V) sorry) sorry

/-- The comparison `etaleBaseChangeToSpacesPullback t V` projects to `t_* V ⟶ T` along
`pullback.snd`. -/
theorem etaleBaseChangeToSpacesPullback_snd {X : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (V : smallEtaleSite X) :
    (etaleBaseChangeToSpacesPullback t V).left ≫ pullback.snd V.hom t =
      etaleBaseChangeHom t V :=
  sorry

/-- The morphism `T ×_X V ⟶ T ×_Y W` associated to an arrow `V ⟶ X ×_Y W` in the spaces
étale site of `X`. -/
def etaleBaseChangeStructuredArrowHom {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj W)) (smallEtaleInclusion X).op) :
    (etaleBaseChange t).obj a.right.unop ⟶ (etaleBaseChange (t ≫ f)).obj W :=
  etaleBaseChangeToSpacesPullback t a.right.unop ≫
    (spacesEtalePullback t).map a.hom.unop ≫ etaleBaseChangeAssocInv t f W

/-- `etaleBaseChangeStructuredArrowHom` is the composite of the spaces-pullback comparison,
the image of the structured arrow, and the inverse associator. -/
theorem etaleBaseChangeStructuredArrowHom_eq {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj W)) (smallEtaleInclusion X).op) :
    etaleBaseChangeStructuredArrowHom t f W a =
      etaleBaseChangeToSpacesPullback t a.right.unop ≫
        (spacesEtalePullback t).map a.hom.unop ≫ etaleBaseChangeAssocInv t f W :=
  rfl

/-- The cone of Kan-counit components presenting `(t ≫ f)_* 𝒪_T ⟶ f_* (t_* 𝒪_T)` at `W`. -/
def commRingPushforwardPrecompCounitCone {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj W))
        (smallEtaleInclusion X).op ⋙
          ((commRingPushforward t).obj (commRingStructureSheaf (ofOver T))).obj) where
  pt :=
    ((commRingPushforward (t ≫ f)).obj (commRingStructureSheaf (ofOver T))).obj.obj (op W)
  π :=
    { app := fun a ↦
        ((smallEtaleInclusion (ofOver T)).op.ran.obj
            (commRingStructureSheaf (ofOver T)).obj).map
          (op (etaleBaseChangeStructuredArrowHom t f W a))
      naturality := fun _ _ _ ↦ sorry }

/-- The component at `W` of the Kan-counit comparison `(t ≫ f)_* 𝒪_T ⟶ f_* (t_* 𝒪_T)`. -/
def commRingPushforwardPrecompCounit_app {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : (smallEtaleSite Y)ᵒᵖ) :
    ((commRingPushforward (t ≫ f)).obj (commRingStructureSheaf (ofOver T))).obj.obj W ⟶
      ((commRingPushforward f).obj
          ((commRingPushforward t).obj (commRingStructureSheaf (ofOver T)))).obj.obj W :=
  limit.lift _ (commRingPushforwardPrecompCounitCone t f W.unop) ≫
    ((smallEtaleInclusion X).op.ranObjObjIsoLimit
        ((commRingPushforward t).obj (commRingStructureSheaf (ofOver T))).obj
        (op ((etaleBaseChange f).obj W.unop))).inv

/-- `commRingPushforwardPrecompCounit_app t f W` is the limit-lift of the Kan-counit cone. -/
theorem commRingPushforwardPrecompCounit_app_eq {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : (smallEtaleSite Y)ᵒᵖ) :
    commRingPushforwardPrecompCounit_app t f W =
      limit.lift _ (commRingPushforwardPrecompCounitCone t f W.unop) ≫
        ((smallEtaleInclusion X).op.ranObjObjIsoLimit
            ((commRingPushforward t).obj (commRingStructureSheaf (ofOver T))).obj
            (op ((etaleBaseChange f).obj W.unop))).inv :=
  rfl

/-- The Kan-counit comparison `(t ≫ f)_* 𝒪_T ⟶ f_* (t_* 𝒪_T)`, obtained from pullback
associativity and the pointwise limit formula for the right Kan extension. -/
def commRingPushforwardPrecompCounit {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) :
    (commRingPushforward (t ≫ f)).obj (commRingStructureSheaf (ofOver T)) ⟶
      (commRingPushforward f).obj
        ((commRingPushforward t).obj (commRingStructureSheaf (ofOver T))) :=
  InducedCategory.homMk
    { app := fun W ↦ commRingPushforwardPrecompCounit_app t f W
      naturality := fun _ _ _ ↦ sorry }

/-- The Kan-counit comparison is an isomorphism of commutative-ring sheaves. -/
instance commRingPushforwardPrecompCounit_isIso {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) :
    IsIso (commRingPushforwardPrecompCounit t f) :=
  sorry

/-- Comparison `f_* (t_* 𝒪_T) ⟶ (t ≫ f)_* 𝒪_T` obtained by inverting the Kan-counit
associator. -/
def commRingPushforwardPrecomp {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) :
    (commRingPushforward f).obj
        ((commRingPushforward t).obj (commRingStructureSheaf (ofOver T))) ⟶
      (commRingPushforward (t ≫ f)).obj (commRingStructureSheaf (ofOver T)) :=
  inv (commRingPushforwardPrecompCounit t f)

/-- `commRingPushforwardPrecomp t f` is the inverse of the Kan-counit comparison. -/
theorem commRingPushforwardPrecomp_eq {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) :
    commRingPushforwardPrecomp t f = inv (commRingPushforwardPrecompCounit t f) :=
  rfl

/-- Restriction of `g_* 𝒪_T` along a morphism of test objects `T' ⟶ T`. -/
def relativeSpectrumTargetMap {X : AlgebraicSpace S} {T T' : Over S}
    (g : ofOver T ⟶ X) (φ : T' ⟶ T) :
    relativeSpectrumTarget g ⟶ relativeSpectrumTarget (ofOverMap φ ≫ g) :=
  CategoryTheory.Under.homMk
    ((commRingPushforward g).map (commRingStructureSheafMap (ofOverMap φ)) ≫
      commRingPushforwardPrecomp (ofOverMap φ) g)
    sorry

/-- An étale atlas scheme of an algebraic space, extracted from the atlas field. -/
def atlasScheme (X : AlgebraicSpace S) : Over S :=
  Classical.choose X.atlas

/-- The atlas morphism `ofOver (atlasScheme X) ⟶ X`. -/
def atlasHom (X : AlgebraicSpace S) : ofOver (atlasScheme X) ⟶ X :=
  Exists.choose (Classical.choose_spec X.atlas)

/-- The atlas morphism is representable and étale as a presheaf morphism. -/
theorem atlasHom_presheaf_etale (X : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (atlasHom X) :=
  (Exists.choose_spec (Classical.choose_spec X.atlas)).1

/-- The atlas morphism is étale as a morphism of algebraic spaces. -/
instance etale_atlasHom (X : AlgebraicSpace S) : Etale (atlasHom X) :=
  sorry

/-- The scheme over `S` associated to an open of the atlas of `X`. -/
def atlasOpenOver (X : AlgebraicSpace S) (V : (atlasScheme X).left.Opens) : Over S :=
  Over.mk (V.ι ≫ (atlasScheme X).hom)

/-- The open immersion of an atlas open, as a morphism over `S`. -/
def atlasOpenOverHom (X : AlgebraicSpace S) (V : (atlasScheme X).left.Opens) :
    atlasOpenOver X V ⟶ atlasScheme X :=
  Over.homMk V.ι rfl

/-- An open immersion of the atlas remains étale after viewing it as a morphism of algebraic
spaces. -/
instance etale_ofOverMap_atlasOpenOverHom (X : AlgebraicSpace S)
    (V : (atlasScheme X).left.Opens) :
    Etale (ofOverMap (atlasOpenOverHom X V)) :=
  sorry

/-- The composite of an atlas open with the atlas morphism is étale. -/
instance etale_atlasOpenHom (X : AlgebraicSpace S) (V : (atlasScheme X).left.Opens) :
    Etale (ofOverMap (atlasOpenOverHom X V) ≫ atlasHom X) :=
  inferInstance

/-- The small étale object of `X` associated to an open of its atlas. -/
def atlasOpenToSmallEtaleObj (X : AlgebraicSpace S) (V : (atlasScheme X).left.Opens) :
    smallEtaleSite X :=
  smallEtaleSite.mk (ofOverMap (atlasOpenOverHom X V) ≫ atlasHom X)

/-- The morphism of atlas opens over `S` induced by an inclusion of opens. -/
def atlasOpenOverMap (X : AlgebraicSpace S) {V W : (atlasScheme X).left.Opens}
    (i : V ⟶ W) : atlasOpenOver X V ⟶ atlasOpenOver X W :=
  Over.homMk ((atlasScheme X).left.homOfLE (leOfHom i)) sorry

/-- The functor from Zariski opens of an étale atlas of `X` to the small étale site of `X`. -/
def atlasOpenToSmallEtale (X : AlgebraicSpace S) :
    (atlasScheme X).left.Opens ⥤ smallEtaleSite X where
  obj := atlasOpenToSmallEtaleObj X
  map {V W} i :=
    MorphismProperty.CostructuredArrow.homMk (atlasOpenOverMap X i) trivial sorry
  map_id := sorry
  map_comp := sorry

/-- Restrict a small étale sheaf of commutative rings on `X` to the Zariski site of an étale
atlas of `X`. -/
def restrictToAtlasPresheaf {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (atlasScheme X).left.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  (atlasOpenToSmallEtale X).op ⋙ F.obj

/-- Restrict an `𝒪_X`-algebra to the Zariski site of an étale atlas of `X`. -/
def restrictUnder {X : AlgebraicSpace S} (B : Under (commRingStructureSheaf X)) :
    Under (restrictToAtlasPresheaf (commRingStructureSheaf X)) :=
  Under.mk (whiskerLeft (atlasOpenToSmallEtale X).op (InducedCategory.Hom.hom B.hom))

/-- Restrict a morphism of `𝒪_X`-algebras to the Zariski site of an étale atlas of `X`. -/
def restrictUnderMap {X : AlgebraicSpace S} {B₁ B₂ : Under (commRingStructureSheaf X)}
    (α : B₁ ⟶ B₂) :
    restrictUnder B₁ ⟶ restrictUnder B₂ :=
  CategoryTheory.Under.homMk
    (whiskerLeft (atlasOpenToSmallEtale X).op (InducedCategory.Hom.hom α.right))
    sorry

/-- The underlying sheaf morphism of `restrictUnderMap α` is whiskering along atlas opens. -/
theorem restrictUnderMap_right {X : AlgebraicSpace S} {B₁ B₂ : Under (commRingStructureSheaf X)}
    (α : B₁ ⟶ B₂) :
    (restrictUnderMap α).right =
      whiskerLeft (atlasOpenToSmallEtale X).op (InducedCategory.Hom.hom α.right) :=
  sorry

/-- The kernel pair scheme `U ×_X U` of the chosen étale atlas of `X`. -/
def atlasKernelPair (X : AlgebraicSpace S) : Over S :=
  (kernelPair (atlasHom X) (atlasHom_presheaf_etale X).rep).left

/-- `atlasKernelPair X` is the source of the represented kernel pair of `atlasHom X`. -/
theorem atlasKernelPair_eq (X : AlgebraicSpace S) :
    atlasKernelPair X = (kernelPair (atlasHom X) (atlasHom_presheaf_etale X).rep).left :=
  rfl

/-- The first projection `t : U ×_X U ⟶ U` of the atlas kernel pair. -/
def atlasKernelPair_t (X : AlgebraicSpace S) : atlasKernelPair X ⟶ atlasScheme X :=
  (kernelPair (atlasHom X) (atlasHom_presheaf_etale X).rep).t

/-- The second projection `s : U ×_X U ⟶ U` of the atlas kernel pair. -/
def atlasKernelPair_s (X : AlgebraicSpace S) : atlasKernelPair X ⟶ atlasScheme X :=
  (kernelPair (atlasHom X) (atlasHom_presheaf_etale X).rep).s

/-- `atlasKernelPair_t X` is the first projection of the represented kernel pair. -/
theorem atlasKernelPair_t_eq (X : AlgebraicSpace S) :
    atlasKernelPair_t X = (kernelPair (atlasHom X) (atlasHom_presheaf_etale X).rep).t :=
  rfl

/-- `atlasKernelPair_s X` is the second projection of the represented kernel pair. -/
theorem atlasKernelPair_s_eq (X : AlgebraicSpace S) :
    atlasKernelPair_s X = (kernelPair (atlasHom X) (atlasHom_presheaf_etale X).rep).s :=
  rfl

/-- The two atlas kernel-pair projections become equal after composition with `atlasHom X`. -/
theorem atlasKernelPair_t_comp_eq_s_comp (X : AlgebraicSpace S) :
    ofOverMap (atlasKernelPair_t X) ≫ atlasHom X =
      ofOverMap (atlasKernelPair_s X) ≫ atlasHom X :=
  sorry

/-- The morphism `ofOver (U ×_X U) ⟶ X` induced by the atlas kernel pair. -/
def atlasKernelPairHom (X : AlgebraicSpace S) : ofOver (atlasKernelPair X) ⟶ X :=
  kernelPairHom (atlasHom X) (atlasHom_presheaf_etale X)

/-- `atlasKernelPairHom X` is the kernel-pair morphism of the atlas. -/
theorem atlasKernelPairHom_eq (X : AlgebraicSpace S) :
    atlasKernelPairHom X = kernelPairHom (atlasHom X) (atlasHom_presheaf_etale X) :=
  rfl

/-- The atlas kernel-pair morphism is étale. -/
instance etale_atlasKernelPairHom (X : AlgebraicSpace S) : Etale (atlasKernelPairHom X) :=
  sorry

/-- The scheme over `S` associated to an open of the atlas kernel pair. -/
def kernelPairOpenOver (X : AlgebraicSpace S) (W : (atlasKernelPair X).left.Opens) : Over S :=
  Over.mk (W.ι ≫ (atlasKernelPair X).hom)

/-- The open immersion of a kernel-pair open, as a morphism over `S`. -/
def kernelPairOpenOverHom (X : AlgebraicSpace S) (W : (atlasKernelPair X).left.Opens) :
    kernelPairOpenOver X W ⟶ atlasKernelPair X :=
  Over.homMk W.ι rfl

/-- An open immersion of the atlas kernel pair remains étale as a morphism of algebraic spaces. -/
instance etale_ofOverMap_kernelPairOpenOverHom (X : AlgebraicSpace S)
    (W : (atlasKernelPair X).left.Opens) :
    Etale (ofOverMap (kernelPairOpenOverHom X W)) :=
  sorry

/-- The composite of a kernel-pair open with the atlas kernel-pair morphism is étale. -/
instance etale_kernelPairOpenHom (X : AlgebraicSpace S) (W : (atlasKernelPair X).left.Opens) :
    Etale (ofOverMap (kernelPairOpenOverHom X W) ≫ atlasKernelPairHom X) :=
  inferInstance

/-- The small étale object of `X` associated to an open of its atlas kernel pair. -/
def kernelPairOpenToSmallEtaleObj (X : AlgebraicSpace S) (W : (atlasKernelPair X).left.Opens) :
    smallEtaleSite X :=
  smallEtaleSite.mk (ofOverMap (kernelPairOpenOverHom X W) ≫ atlasKernelPairHom X)

/-- The structural morphism of `kernelPairOpenToSmallEtaleObj X W` is the composite with
`atlasKernelPairHom X`. -/
theorem kernelPairOpenToSmallEtaleObj_hom (X : AlgebraicSpace S)
    (W : (atlasKernelPair X).left.Opens) :
    (kernelPairOpenToSmallEtaleObj X W).hom =
      ofOverMap (kernelPairOpenOverHom X W) ≫ atlasKernelPairHom X :=
  sorry

/-- The morphism of kernel-pair opens over `S` induced by an inclusion of opens. -/
def kernelPairOpenOverMap (X : AlgebraicSpace S) {V W : (atlasKernelPair X).left.Opens}
    (i : V ⟶ W) : kernelPairOpenOver X V ⟶ kernelPairOpenOver X W :=
  Over.homMk ((atlasKernelPair X).left.homOfLE (leOfHom i)) sorry

/-- The functor from Zariski opens of `U ×_X U` to the small étale site of `X`. -/
def kernelPairOpenToSmallEtale (X : AlgebraicSpace S) :
    (atlasKernelPair X).left.Opens ⥤ smallEtaleSite X where
  obj := kernelPairOpenToSmallEtaleObj X
  map {V W} i :=
    MorphismProperty.CostructuredArrow.homMk (kernelPairOpenOverMap X i) trivial sorry
  map_id := sorry
  map_comp := sorry

/-- On objects, `kernelPairOpenToSmallEtale X` is `kernelPairOpenToSmallEtaleObj X`. -/
theorem kernelPairOpenToSmallEtale_obj (X : AlgebraicSpace S)
    (W : (atlasKernelPair X).left.Opens) :
    (kernelPairOpenToSmallEtale X).obj W = kernelPairOpenToSmallEtaleObj X W :=
  rfl

/-- Restriction of a small étale sheaf of commutative rings on `X` to the Zariski site of
`U ×_X U`. -/
def restrictToKernelPairPresheaf {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (atlasKernelPair X).left.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  (kernelPairOpenToSmallEtale X).op ⋙ F.obj

/-- `restrictToKernelPairPresheaf F` is precomposition with `kernelPairOpenToSmallEtale`. -/
theorem restrictToKernelPairPresheaf_eq {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    restrictToKernelPairPresheaf F = (kernelPairOpenToSmallEtale X).op ⋙ F.obj :=
  rfl

/-- The image of a kernel-pair open under an atlas kernel-pair projection. -/
def atlasKernelPairImage (X : AlgebraicSpace S) (φ : atlasKernelPair X ⟶ atlasScheme X)
    (W : (atlasKernelPair X).left.Opens) : (atlasScheme X).left.Opens :=
  ⟨φ.left.base '' (W : Set _), sorry⟩

/-- The carrier of `atlasKernelPairImage X φ W` is the image of `W` under `φ`. -/
theorem atlasKernelPairImage_coe (X : AlgebraicSpace S)
    (φ : atlasKernelPair X ⟶ atlasScheme X) (W : (atlasKernelPair X).left.Opens) :
    (atlasKernelPairImage X φ W : Set _) = φ.left.base '' (W : Set _) :=
  rfl

/-- The morphism of schemes over `S` from a kernel-pair open to its image in the atlas. -/
def atlasKernelPairOpenOverHom (X : AlgebraicSpace S)
    (φ : atlasKernelPair X ⟶ atlasScheme X) (W : (atlasKernelPair X).left.Opens) :
    kernelPairOpenOver X W ⟶ atlasOpenOver X (atlasKernelPairImage X φ W) :=
  Over.homMk (φ.left.resLE (atlasKernelPairImage X φ W) W sorry) sorry

/-- The morphism of small étale objects over `X` from a kernel-pair open to its image in the
atlas. -/
def kernelPairOpenHom (X : AlgebraicSpace S) (φ : atlasKernelPair X ⟶ atlasScheme X)
    (W : (atlasKernelPair X).left.Opens) :
    kernelPairOpenToSmallEtaleObj X W ⟶
      atlasOpenToSmallEtaleObj X (atlasKernelPairImage X φ W) :=
  MorphismProperty.CostructuredArrow.homMk (atlasKernelPairOpenOverHom X φ W) trivial sorry

/-- The underlying scheme morphism of `kernelPairOpenHom X φ W` is
`atlasKernelPairOpenOverHom X φ W`. -/
theorem kernelPairOpenHom_left (X : AlgebraicSpace S)
    (φ : atlasKernelPair X ⟶ atlasScheme X) (W : (atlasKernelPair X).left.Opens) :
    (kernelPairOpenHom X φ W).left = atlasKernelPairOpenOverHom X φ W :=
  rfl

/-- An atlas-Zariski algebra map is compatible with a kernel-pair algebra map along an atlas
kernel-pair projection when the naturality squares on images of kernel-pair opens commute. -/
def isCompatibleWithKernelPairProjection {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (φ : atlasKernelPair X ⟶ atlasScheme X)
    (e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g))
    (k : restrictToKernelPairPresheaf A.obj.right ⟶
      restrictToKernelPairPresheaf (relativeSpectrumTarget g).right) : Prop :=
  ∀ W : (atlasKernelPair X).left.Opens,
    e.right.app (op (atlasKernelPairImage X φ W)) ≫
        (relativeSpectrumTarget g).right.obj.map (op (kernelPairOpenHom X φ W)) =
      A.obj.right.obj.map (op (kernelPairOpenHom X φ W)) ≫ k.app (op W)

/-- An atlas-Zariski `𝒪_X`-algebra map is descended when the two pullbacks along the
projections of `U ×_X U` agree as a map on the Zariski site of the kernel pair. -/
def isDescendedAtlasAlgebraMap {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X}
    (e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g)) : Prop :=
  ∃ k : restrictToKernelPairPresheaf A.obj.right ⟶
      restrictToKernelPairPresheaf (relativeSpectrumTarget g).right,
    isCompatibleWithKernelPairProjection (atlasKernelPair_t X) e k ∧
      isCompatibleWithKernelPairProjection (atlasKernelPair_s X) e k

/-- Compatibility along an atlas kernel-pair projection is the naturality square on each
kernel-pair open. -/
theorem isCompatibleWithKernelPairProjection_iff {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (φ : atlasKernelPair X ⟶ atlasScheme X)
    (e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g))
    (k : restrictToKernelPairPresheaf A.obj.right ⟶
      restrictToKernelPairPresheaf (relativeSpectrumTarget g).right) :
    isCompatibleWithKernelPairProjection φ e k ↔
      ∀ W : (atlasKernelPair X).left.Opens,
        e.right.app (op (atlasKernelPairImage X φ W)) ≫
            (relativeSpectrumTarget g).right.obj.map (op (kernelPairOpenHom X φ W)) =
          A.obj.right.obj.map (op (kernelPairOpenHom X φ W)) ≫ k.app (op W) :=
  sorry

/-- Descent of an atlas algebra map is existence of a common kernel-pair algebra map compatible
with both projections. -/
theorem isDescendedAtlasAlgebraMap_iff {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X}
    (e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g)) :
    isDescendedAtlasAlgebraMap e ↔
      ∃ k : restrictToKernelPairPresheaf A.obj.right ⟶
          restrictToKernelPairPresheaf (relativeSpectrumTarget g).right,
        isCompatibleWithKernelPairProjection (atlasKernelPair_t X) e k ∧
          isCompatibleWithKernelPairProjection (atlasKernelPair_s X) e k :=
  sorry

/-- Type `u` encoding of an `𝒪_X`-algebra map `A ⟶ g_* 𝒪_T`: a morphism of the restrictions of
both algebras to the Zariski site of an étale atlas of `X` that is invariant under the two
pullbacks to the Zariski site of `U ×_X U`. -/
def relativeSpectrumAlgebraMap {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    {T : Over S} (g : ofOver T ⟶ X) : Type u :=
  { e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g) //
    isDescendedAtlasAlgebraMap e }

/-- The underlying atlas-Zariski morphism of a descended algebra map. -/
def relativeSpectrumAlgebraMap.val {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (e : relativeSpectrumAlgebraMap A g) :
    restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g) :=
  e.1

/-- `relativeSpectrumAlgebraMap.val e` is the first component of the descended subtype. -/
theorem relativeSpectrumAlgebraMap.val_eq {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (e : relativeSpectrumAlgebraMap A g) :
    relativeSpectrumAlgebraMap.val e = e.1 :=
  rfl

/-- Restrict an `𝒪_X`-algebra map `A ⟶ g_* 𝒪_T` to the Type `u` descended atlas encoding. -/
def relativeSpectrumAlgebraMap.ofHom {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (α : A.obj ⟶ relativeSpectrumTarget g) :
    relativeSpectrumAlgebraMap A g :=
  ⟨restrictUnderMap α, sorry⟩

/-- `ofHom` is restriction of algebra maps to the descended atlas subtype. -/
theorem relativeSpectrumAlgebraMap.ofHom_val {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (α : A.obj ⟶ relativeSpectrumTarget g) :
    (relativeSpectrumAlgebraMap.ofHom α).1 = restrictUnderMap α :=
  rfl

/-- Restriction from global `𝒪_X`-algebra maps `A ⟶ g_* 𝒪_T` to descended atlas-Zariski maps
is bijective. -/
theorem relativeSpectrumAlgebraMap.restrict_bijective {X : AlgebraicSpace S}
    {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X} :
    Function.Bijective
      (relativeSpectrumAlgebraMap.ofHom (A := A) (g := g)) :=
  sorry

/-- Yoneda inversion recovers a morphism of algebraic spaces from its `T`-point. -/
theorem yonedaEquiv_symm_yonedaEquiv_hom {X : AlgebraicSpace S} {T : Over S}
    (toX : ofOver T ⟶ X) :
    yonedaEquiv.symm (yonedaEquiv (toX : yoneda.obj T ⟶ X.functorOfPoints)) = toX :=
  sorry

/-- A `T`-point of the relative spectrum of a quasi-coherent `𝒪_X`-algebra. -/
abbrev relativeSpectrumPair {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) (T : Over S) :
    Type u :=
  Σ toX : X.functorOfPoints.obj (op T),
    relativeSpectrumAlgebraMap A (yonedaEquiv.symm toX)

/-- Build a relative-spectrum point from a morphism to `X` and an `𝒪_X`-algebra map into the
pushforward of `𝒪_T`. -/
def relativeSpectrumPairMk {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T : Over S}
    (toX : ofOver T ⟶ X) (algebraMap : A.obj ⟶ relativeSpectrumTarget toX) :
    relativeSpectrumPair A T :=
  ⟨yonedaEquiv (toX : yoneda.obj T ⟶ X.functorOfPoints),
    relativeSpectrumAlgebraMap.ofHom
      (algebraMap ≫
        eqToHom
          (congrArg relativeSpectrumTarget
            (Equiv.symm_apply_apply yonedaEquiv toX).symm))⟩

/-- The structure morphism of `relativeSpectrumPairMk g α` is the `T`-point of `X` associated
to `g`. -/
theorem relativeSpectrumPairMk_fst {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T : Over S}
    (toX : ofOver T ⟶ X) (algebraMap : A.obj ⟶ relativeSpectrumTarget toX) :
    (relativeSpectrumPairMk toX algebraMap).1 =
      yonedaEquiv (toX : yoneda.obj T ⟶ X.functorOfPoints) :=
  rfl

/-- The algebra map of `relativeSpectrumPairMk g α` is the atlas restriction of `α`. -/
theorem relativeSpectrumPairMk_snd {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T : Over S}
    (toX : ofOver T ⟶ X) (algebraMap : A.obj ⟶ relativeSpectrumTarget toX) :
    (relativeSpectrumPairMk toX algebraMap).2 =
      relativeSpectrumAlgebraMap.ofHom
        (algebraMap ≫
          eqToHom
            (congrArg relativeSpectrumTarget
              (Equiv.symm_apply_apply yonedaEquiv toX).symm)) :=
  rfl

/-- Pull a relative-spectrum point back along a morphism of schemes over `S`. -/
def relativeSpectrumPairMap {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T T' : Over S}
    (φ : T' ⟶ T) (p : relativeSpectrumPair A T) : relativeSpectrumPair A T' :=
  ⟨yonedaEquiv (ofOverMap φ ≫ yonedaEquiv.symm p.1 : yoneda.obj T' ⟶ X.functorOfPoints),
    cast
      (congrArg (fun γ : ofOver T' ⟶ X ↦ relativeSpectrumAlgebraMap A γ)
        (Equiv.symm_apply_apply yonedaEquiv
          (ofOverMap φ ≫ yonedaEquiv.symm p.1)).symm)
      ⟨p.2.1 ≫ restrictUnderMap (relativeSpectrumTargetMap (yonedaEquiv.symm p.1) φ),
        sorry⟩⟩

/-- The structure morphism of a pulled-back point is the composite with `ofOverMap φ`. -/
theorem relativeSpectrumPairMap_fst {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T T' : Over S} (φ : T' ⟶ T) (p : relativeSpectrumPair A T) :
    (relativeSpectrumPairMap φ p).1 =
      yonedaEquiv
        ((ofOverMap φ ≫ yonedaEquiv.symm p.1 : yoneda.obj T' ⟶ X.functorOfPoints)) :=
  sorry

/-- The action on relative-spectrum points induced by a morphism in `(Over S)ᵒᵖ`. -/
def relativeSpectrumFunctorMap {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    {T T' : (Over S)ᵒᵖ} (i : T ⟶ T') :
    relativeSpectrumPair A T.unop → relativeSpectrumPair A T'.unop :=
  relativeSpectrumPairMap i.unop

/-- The functor of points of the relative spectrum of a quasi-coherent `𝒪_X`-algebra. -/
def relativeSpectrumFunctor {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := relativeSpectrumPair A T.unop
  map i := TypeCat.ofHom (relativeSpectrumFunctorMap A i)
  map_id := sorry
  map_comp := sorry

/-- Evaluating the relative-spectrum functor on a scheme over `S` recovers the point type. -/
theorem relativeSpectrumFunctor_obj {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (T : Over S) :
    (relativeSpectrumFunctor A).obj (op T) = relativeSpectrumPair A T :=
  rfl

/-- The relative spectrum of a quasi-coherent `𝒪_X`-algebra, as an algebraic space over `S`. -/
def relativeSpec {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) : AlgebraicSpace S :=
  ofFunctor (relativeSpectrumFunctor A) sorry sorry sorry

/-- The functor of points of `relativeSpec A` is `relativeSpectrumFunctor A`. -/
theorem relativeSpec_functorOfPoints {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (relativeSpec A).functorOfPoints = relativeSpectrumFunctor A :=
  rfl

/-- The structure morphism `Spec_X(A) ⟶ X`, forgetting algebra data. -/
def relativeSpecπ {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    relativeSpec A ⟶ X where
  app T := TypeCat.ofHom fun p ↦ p.1
  naturality := sorry

/-- The component of `relativeSpecπ A` at `T` is the underlying morphism to `X`. -/
theorem relativeSpecπ_app {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) (T : (Over S)ᵒᵖ)
    (p : relativeSpectrumPair A T.unop) :
    (relativeSpecπ A).app T p = p.1 :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
