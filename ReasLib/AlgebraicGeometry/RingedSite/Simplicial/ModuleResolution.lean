/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.LowerShriek
public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationTopos

/-!
# Canonical module resolution of a ringed site augmentation

The lower-shriek images of stagewise module pullbacks form an augmented simplicial
object and its alternating-face complex.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w uD vD

namespace CategoryTheory.SimplicialSites

section

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {D : RingedSite.{uD, vD, w}}
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable (a : ToposHom (totalRingedSite C J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp a).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} D.structureSheaf)

/-- Continuous-site comparison `f_φ^*(a_n^* G) ⟶ g_m^*(a^* G)` from the mate of
`stageInclusionWhisker`. -/
private def modulePullbackStageCompAux {n m : SimplexCategory} (φ : n ⟶ m) :
    (ringedToposMap_pullback C J O φ).obj
      (((stageMorphism C J O n).comp a).modulePullback.obj G) ⟶
      (Cocontinuous.moduleInverseImage (ofStage C m) O).obj (a.modulePullback.obj G) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (ringedToposMapDirectStructure C J O φ)).homEquiv
      (((stageMorphism C J O n).comp a).modulePullback.obj G)
      ((Cocontinuous.moduleInverseImage (ofStage C m) O).obj
        (a.modulePullback.obj G))).symm
    ((ToposHom.modulePullbackCompIso (stageMorphism C J O n) a).hom.app G ≫
      (moduleInverseImageIsoModulePullback C J O n).inv.app
        (a.modulePullback.obj G) ≫
      (SheafOfModules.pushforwardNatTrans (𝟙 (componentRingSheaf C J O n))
          (stageInclusionWhisker C φ)).app (a.modulePullback.obj G) ≫
      (SheafOfModules.pushforwardComp (ringedToposMapDirectStructure C J O φ)
          (𝟙 (componentRingSheaf C J O m))).inv.app (a.modulePullback.obj G))

/-- Restriction `f_φ^*(a_n^* G) ⟶ a_m^* G` along the simplicial 2-cell. -/
def modulePullbackStageComp {n m : SimplexCategory} (φ : n ⟶ m) :
    (ringedToposMap C J O φ).modulePullback.obj
      (((stageMorphism C J O n).comp a).modulePullback.obj G) ⟶
      ((stageMorphism C J O m).comp a).modulePullback.obj G :=
  (ringedToposMap_pullbackIso C J O φ).inv.app
      (((stageMorphism C J O n).comp a).modulePullback.obj G) ≫
    modulePullbackStageCompAux C J O a G φ ≫
    (moduleInverseImageIsoModulePullback C J O m).hom.app (a.modulePullback.obj G) ≫
    (ToposHom.modulePullbackCompIso (stageMorphism C J O m) a).inv.app G


end

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (forget RingCat.{w})]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos C J K u0).ringDirectImage.obj O)

/-- The ringed morphism induced by a site augmentation and a map from the target
structure sheaf to the direct image of the total structure sheaf. -/
def IsAugmentation.ringedHom :
    ToposHom (totalRingedSite C J O) (ofRingSheaf K.toGrothendieck O_D) where
  toTopos := IsAugmentation.totalTopos C J K u0
  structureMap :=
    ((IsAugmentation.totalTopos C J K u0).ringAdjunction.homEquiv O_D O).symm aSharp

/-- The underlying topos morphism is the total augmentation. -/
theorem IsAugmentation.ringedHom_toTopos :
    (IsAugmentation.ringedHom C J K u0 O O_D aSharp).toTopos =
      IsAugmentation.totalTopos C J K u0 := rfl

/-- The structure map is the inverse ring-adjunction mate of the given direct-image map. -/
theorem IsAugmentation.ringedHom_structureMap :
    (IsAugmentation.ringedHom C J K u0 O O_D aSharp).structureMap =
      ((IsAugmentation.totalTopos C J K u0).ringAdjunction.homEquiv O_D O).symm aSharp := rfl

variable [UnivLE.{max u v, w}]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [(SheafOfModules.restrictScalars.{w} (IsAugmentation.ringedHom C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} O_D)

/-- The augmentation identifies the two composite inverse-image functors. -/
private def augmentationStageInverseImageCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ((stageMorphism C J O n).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).toTopos.inverseImage ⋙
        (ringedToposMap C J O φ).toTopos.inverseImage ≅
      ((stageMorphism C J O m).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).toTopos.inverseImage :=
  Functor.isoWhiskerRight (IsAugmentation.totalTopos_comp_ofStage C J K u0 n)
      (toposMap C J φ).inverseImage ≪≫
    IsAugmentation.stageTopos_comp C J K u0 φ ≪≫
      (IsAugmentation.totalTopos_comp_ofStage C J K u0 m).symm

/-- The same augmentation identity on underlying direct images, as a mate of the
explicit inverse-image isomorphism. -/
private def augmentationStagePushforwardCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    (ringedToposMap C J O φ).toTopos.pushforward ⋙
        ((stageMorphism C J O n).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).toTopos.pushforward ≅
      ((stageMorphism C J O m).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).toTopos.pushforward :=
  ((((stageMorphism C J O n).comp
      (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).toTopos.adjunction.comp
        (ringedToposMap C J O φ).toTopos.adjunction).ofNatIsoLeft
      (augmentationStageInverseImageCompIso C J K u0 O O_D aSharp φ)).rightAdjointUniq
    ((stageMorphism C J O m).comp
      (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).toTopos.adjunction

/-- Lift the specified direct-image mate to modules, retaining its forward and inverse
functions. Linearity is the compatibility of `aSharp` with the simplicial transitions. -/
private def augmentationStageModulePushforwardCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    (ringedToposMap C J O φ).modulePushforward ⋙
        ((stageMorphism C J O n).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward ≅
      ((stageMorphism C J O m).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward := by
  let f := ringedToposMap C J O φ
  let a_n := (stageMorphism C J O n).comp
    (IsAugmentation.ringedHom C J K u0 O O_D aSharp)
  let a_m := (stageMorphism C J O m).comp
    (IsAugmentation.ringedHom C J K u0 O O_D aSharp)
  let e := Functor.associator f.modulePushforward a_n.modulePushforward
      (Sheaf.InternalModule.ToInternal.underlying O_D) ≪≫
    Functor.isoWhiskerLeft f.modulePushforward (ToposHom.ModulePushforward.forgetIso a_n) ≪≫
    (Functor.associator f.modulePushforward
      (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n))
      a_n.toTopos.pushforward).symm ≪≫
    Functor.isoWhiskerRight (ToposHom.ModulePushforward.forgetIso f) a_n.toTopos.pushforward ≪≫
    Functor.associator
      (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O m))
      f.toTopos.pushforward a_n.toTopos.pushforward ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O m))
      (augmentationStagePushforwardCompIso C J K u0 O O_D aSharp φ) ≪≫
    (ToposHom.ModulePushforward.forgetIso a_m).symm
  exact Sheaf.InternalModule.functorIsoOfUnderlying O_D e (by sorry) (by sorry)

/-- Inverse-image form of `a_n ∘ f_φ = a_m` on modules. The reverse map is the original
simplicial comparison; its inverse is the explicit mate of the augmentation identity. -/
def modulePullbackStageCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ((stageMorphism C J O m).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G ≅
      (ringedToposMap C J O φ).modulePullback.obj
        (((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G) :=
  { hom :=
      (((((stageMorphism C J O n).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).moduleAdjunction.comp
            (ringedToposMap C J O φ).moduleAdjunction).ofNatIsoRight
          (augmentationStageModulePushforwardCompIso C J K u0 O O_D aSharp φ)).leftAdjointUniq
        ((stageMorphism C J O m).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).moduleAdjunction).inv.app G
    inv := modulePullbackStageComp C J O
      (IsAugmentation.ringedHom C J K u0 O O_D aSharp) G φ
    hom_inv_id := by sorry
    inv_hom_id := by sorry }

/-- The inverse component of the augmentation isomorphism is the specified stage comparison. -/
@[simp]
theorem modulePullbackStageCompIso_inv {n m : SimplexCategory} (φ : n ⟶ m) :
    (modulePullbackStageCompIso C J K u0 O O_D aSharp G φ).inv =
      modulePullbackStageComp C J O
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp) G φ := rfl

/-- Stage pullback comparisons for a ringed augmentation are invertible. -/
instance modulePullbackStageComp_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (modulePullbackStageComp C J O (IsAugmentation.ringedHom C J K u0 O O_D aSharp) G φ) :=
  (modulePullbackStageCompIso C J K u0 O O_D aSharp G φ).isIso_inv

/-- The structure map `g_{m!}(a_m^* G) ⟶ g_{n!}(a_n^* G)` induced by a simplex
operator `φ : n ⟶ m`. -/
def lowerShriekModulePullback_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (moduleLowerShriek C J O m).obj
      (((stageMorphism C J O m).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G) ⟶
    (moduleLowerShriek C J O n).obj
      (((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G) :=
  ((moduleLowerShriek.adjunction C J O m).homEquiv
      (((stageMorphism C J O m).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G)
      ((moduleLowerShriek C J O n).obj
        (((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G))).symm
    ((modulePullbackStageCompIso C J K u0 O O_D aSharp G φ).hom ≫
      moduleLowerShriek_component C J O φ
        (((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G) ≫
      (moduleInverseImageIsoModulePullback C J O m).inv.app
        ((moduleLowerShriek C J O n).obj
          (((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G)))

/-- Identity simplex operators induce identity structure maps of
`n ↦ g_{n!}(a_n^* G)`. -/
theorem lowerShriekModulePullback_map_id (n : SimplexCategory) :
    lowerShriekModulePullback_map C J K u0 O O_D aSharp G (𝟙 n) =
      𝟙 ((moduleLowerShriek C J O n).obj
        (((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!}(a_n^* G)` are functorial in simplex operators. -/
theorem lowerShriekModulePullback_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    lowerShriekModulePullback_map C J K u0 O O_D aSharp G (ψ ≫ φ) =
      lowerShriekModulePullback_map C J K u0 O O_D aSharp G φ ≫
        lowerShriekModulePullback_map C J K u0 O O_D aSharp G ψ :=
  sorry

/-- The simplicial sheaf of `O`-modules `n ↦ g_{n!}(a_n^* G)` on the total site. -/
def lowerShriekModulePullback : SimplicialObject (SheafOfModules.{w} O) where
  obj n :=
    (moduleLowerShriek C J O n.unop).obj
      (((stageMorphism C J O n.unop).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G)
  map f := lowerShriekModulePullback_map C J K u0 O O_D aSharp G f.unop
  map_id n := lowerShriekModulePullback_map_id C J K u0 O O_D aSharp G n.unop
  map_comp f g := lowerShriekModulePullback_map_comp C J K u0 O O_D aSharp G g.unop f.unop

/-- The value of `lowerShriekModulePullback` at `n` is `g_{n!}(a_n^* G)`. -/
theorem lowerShriekModulePullback_obj (n : SimplexCategory) :
    (lowerShriekModulePullback C J K u0 O O_D aSharp G).obj (op n) =
      (moduleLowerShriek C J O n).obj
        (((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G) :=
  rfl

/-- The face map `d_i : g_{(n+1)!}(a_{n+1}^* G) ⟶ g_{n!}(a_n^* G)`. -/
def modulePullbackFace (n : ℕ) (i : Fin (n + 2)) :
    (lowerShriekModulePullback C J K u0 O O_D aSharp G).obj (op ⦋n + 1⦌) ⟶
      (lowerShriekModulePullback C J K u0 O O_D aSharp G).obj (op ⦋n⦌) :=
  (lowerShriekModulePullback C J K u0 O O_D aSharp G).δ i


/-- The component of the augmentation `g_{n!}(a_n^* G) ⟶ a^* G` at a simplex `n`. -/
def modulePullbackAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (lowerShriekModulePullback C J K u0 O O_D aSharp G).obj n ⟶ (IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G :=
  ((moduleLowerShriek.adjunction C J O n.unop).homEquiv
      (((stageMorphism C J O n.unop).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G)
      ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G)).symm
    ((ToposHom.modulePullbackCompIso (stageMorphism C J O n.unop) (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).hom.app G ≫
      (moduleInverseImageIsoModulePullback C J O n.unop).inv.app
        ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G))

/-- Naturality of the degreewise augmentation `g_{n!}(a_n^* G) ⟶ a^* G`. -/
theorem modulePullbackAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (lowerShriekModulePullback C J K u0 O O_D aSharp G).map f ≫
          modulePullbackAugmented_hom_app C J K u0 O O_D aSharp G m =
        modulePullbackAugmented_hom_app C J K u0 O O_D aSharp G n ≫
          ((SimplicialObject.const _).obj ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G)).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!}(a_n^* G) ⟶ const (a^* G)`. -/
def modulePullbackAugmented_hom :
    lowerShriekModulePullback C J K u0 O O_D aSharp G ⟶
      (SimplicialObject.const _).obj ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G) where
  app := modulePullbackAugmented_hom_app C J K u0 O O_D aSharp G
  naturality := modulePullbackAugmented_hom_naturality C J K u0 O O_D aSharp G

/-- The augmented simplicial object of `g_{n!}(a_n^* G)` over `a^* G`. -/
def modulePullbackAugmented : SimplicialObject.Augmented (SheafOfModules.{w} O) where
  left := lowerShriekModulePullback C J K u0 O O_D aSharp G
  right := (IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G
  hom := modulePullbackAugmented_hom C J K u0 O O_D aSharp G

/-- The alternating-face chain complex
`… → g_{2!}(a_2^* G) → g_{1!}(a_1^* G) → g_{0!}(a_0^* G)`. -/
abbrev modulePullbackComplex : ChainComplex (SheafOfModules.{w} O) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (modulePullbackAugmented C J K u0 O O_D aSharp G))

/-- Degree `n` of `modulePullbackComplex` is the sheaf of modules `g_{n!}(a_n^* G)`. -/
theorem modulePullbackComplex_X (n : ℕ) :
    (modulePullbackComplex C J K u0 O O_D aSharp G).X n =
      (moduleLowerShriek C J O ⦋n⦌).obj
        (((stageMorphism C J O ⦋n⦌).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePullback.obj G) :=
  rfl

/-- Differentials of `modulePullbackComplex` are the alternating sums of face maps. -/
theorem modulePullbackComplex_d_eq (n : ℕ) :
    (modulePullbackComplex C J K u0 O O_D aSharp G).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • modulePullbackFace C J K u0 O O_D aSharp G n i := by
    exact alternatingFaceMapComplex_obj_d _ n

/-- The canonical chain-map augmentation from `modulePullbackComplex` to `a^* G`
concentrated in degree zero. -/
def modulePullbackAugmentation :
    modulePullbackComplex C J K u0 O O_D aSharp G ⟶
      (ChainComplex.single₀ _).obj ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G) :=
  AlternatingFaceMapComplex.ε.app (modulePullbackAugmented C J K u0 O O_D aSharp G)

/-- The degree-zero component of `modulePullbackAugmentation` is the simplicial
augmentation at `⦋0⦌`. -/
theorem modulePullbackAugmentation_f_zero :
    (modulePullbackAugmentation C J K u0 O O_D aSharp G).f 0 =
      (modulePullbackAugmented C J K u0 O O_D aSharp G).hom.app (op ⦋0⦌) :=
  AlternatingFaceMapComplex.ε_app_f_zero _

/-- The canonical alternating-face augmentation of the module inverse image along a
site augmentation is a quasi-isomorphism. -/
instance modulePullbackAugmentation_quasiIso :
    QuasiIso
      (modulePullbackAugmentation C J K u0 O O_D aSharp G :
        modulePullbackComplex C J K u0 O O_D aSharp G ⟶
          (ChainComplex.single₀ _).obj ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G)) :=
  sorry

end CategoryTheory.SimplicialSites
