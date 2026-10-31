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
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Fiber
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationTopos

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

namespace CategoryTheory.Grothendieck

section

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {D : RingedSite.{uD, vD, w}}
variable [D.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable (a : ToposHom (fiberTotalRingedSite F J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp a).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} D.structureSheaf)

/-- Continuous restriction of `a^* G` along the degree-`n` fiber inclusion. -/
private def fiberAugmentation_stage_underlyingIso (n : SimplexCategory) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ≅
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj (a.modulePullback.obj G)) :=
  (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).mapIso
      ((ToposHom.modulePullbackCompIso (fiberStageMorphism F J O n) a).app G) ≪≫
    fiberModulePullback_underlyingIso F J O n (a.modulePullback.obj G)

/-- The `ιNatTrans` 2-cell on underlying type-valued sheaves of `a_n^* G` and `a_m^* G`. -/
private def fiberModulePullbackStageComp_underlying {n m : SimplexCategory} (φ : n ⟶ m) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj
      ((Sheaf.InternalModule.ToInternal.underlying
          (fiberComponentRingSheaf F J O n)).obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G)) ⟶
      ((ι F (op m)).sheafPushforwardContinuous (Type w)
        (J (op m)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          (a.modulePullback.obj G)) :=
  (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerLeft (F.map φ.op).toFunctor.op
        ((sheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).map
          (fiberAugmentation_stage_underlyingIso F J O a G n).hom)) ≫
    (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerRight (NatTrans.op (ιNatTrans φ.op))
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          (a.modulePullback.obj G)).obj) ≫
    (sheafificationAdjunction ((J (op m)).toGrothendieck) (Type w)).counit.app
      (((ι F (op m)).sheafPushforwardContinuous (Type w)
          (J (op m)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          (a.modulePullback.obj G)))

/-- Geometric inverse-image comparison `f_φ^{-1}(a_n^* G) ⟶ restrict(a_m^* G)` along
`ιNatTrans`. -/
def fiberModulePullbackStageComp_geometric {n m : SimplexCategory} (φ : n ⟶ m) :
    ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
        (fiberComponentRingSheaf F J O n)).obj
      (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ⟶
      (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj
        (((fiberStageMorphism F J O m).comp a).modulePullback.obj G) := by
    let R := (fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
      (fiberComponentRingSheaf F J O n)
    let M := ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
      (fiberComponentRingSheaf F J O n)).obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G)
    let N := (SheafOfModules.restrictScalars
      (fiberRingedToposMap F J O φ).structureMap).obj
        (((fiberStageMorphism F J O m).comp a).modulePullback.obj G)
    let α : (Sheaf.InternalModule.ToInternal.underlying R).obj M ⟶
        (Sheaf.InternalModule.ToInternal.underlying R).obj N :=
      (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImageForgetIso
        (fiberComponentRingSheaf F J O n)).hom.app
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ≫
      fiberModulePullbackStageComp_underlying F J O a G φ ≫
      (fiberAugmentation_stage_underlyingIso F J O a G m).inv ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ
          (((fiberStageMorphism F J O m).comp a).modulePullback.obj G)).inv)
    have h :
        (∀ U (x y : M.val.obj U),
          Sheaf.InternalModule.underlyingApp R α U (x + y) =
            Sheaf.InternalModule.underlyingApp R α U x +
              Sheaf.InternalModule.underlyingApp R α U y) ∧
        (∀ U (r : R.obj.obj U) (x : M.val.obj U),
          Sheaf.InternalModule.underlyingApp R α U (r • x) =
            r • Sheaf.InternalModule.underlyingApp R α U x) := by
      sorry
    exact Sheaf.InternalModule.homOfUnderlying R α h.1 h.2

/-- Restriction `f_φ^*(a_n^* G) ⟶ a_m^* G` along the simplicial 2-cell. -/
def fiberModulePullbackStageComp {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberRingedToposMap F J O φ).modulePullback.obj
      (((fiberStageMorphism F J O n).comp a).modulePullback.obj G) ⟶
      ((fiberStageMorphism F J O m).comp a).modulePullback.obj G :=
  (ToposHom.ModulePullback.scalarHomEquiv (fiberRingedToposMap F J O φ)
      (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
          (fiberComponentRingSheaf F J O n)).obj
        (((fiberStageMorphism F J O n).comp a).modulePullback.obj G))
      (((fiberStageMorphism F J O m).comp a).modulePullback.obj G)).symm
    (fiberModulePullbackStageComp_geometric F J O a G φ)


end

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos F J K u0).ringDirectImage.obj O)

/-- The ringed morphism induced by a site augmentation and a map from the target
structure sheaf to the direct image of the total structure sheaf. -/
def IsAugmentation.ringedHom :
    ToposHom (fiberTotalRingedSite F J O) (ofRingSheaf K.toGrothendieck O_D) where
  toTopos := IsAugmentation.totalTopos F J K u0
  structureMap :=
    ((IsAugmentation.totalTopos F J K u0).ringAdjunction.homEquiv O_D O).symm aSharp

/-- The underlying topos morphism is the total augmentation. -/
theorem IsAugmentation.ringedHom_toTopos :
    (IsAugmentation.ringedHom F J K u0 O O_D aSharp).toTopos =
      IsAugmentation.totalTopos F J K u0 := rfl

/-- The structure map is the inverse ring-adjunction mate of the given direct-image map. -/
theorem IsAugmentation.ringedHom_structureMap :
    (IsAugmentation.ringedHom F J K u0 O O_D aSharp).structureMap =
      ((IsAugmentation.totalTopos F J K u0).ringAdjunction.homEquiv O_D O).symm aSharp := rfl

variable [UnivLE.{max u v, w}]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [(SheafOfModules.restrictScalars.{w} (IsAugmentation.ringedHom F J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} O_D)

/-- The augmentation's stage-composition identification on underlying inverse images. -/
private def fiberModulePullbackStageInverseImageIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ((fiberRingedToposMap F J O φ).comp
        ((fiberStageMorphism F J O n).comp
          (IsAugmentation.ringedHom F J K u0 O O_D aSharp))).toTopos.inverseImage ≅
      ((fiberStageMorphism F J O m).comp
        (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).toTopos.inverseImage :=
  Functor.isoWhiskerRight
      (IsAugmentation.totalTopos_comp_fiberMorphism F J K u0 n)
      (toposMap F J φ).inverseImage ≪≫
    IsAugmentation.stageTopos_comp F J K u0 φ ≪≫
    (IsAugmentation.totalTopos_comp_fiberMorphism F J K u0 m).symm

/-- The same identification is compatible with the ring map supplied by `aSharp`. -/
private def fiberModulePullbackStageTwoIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ToposHom.TwoIso
      ((fiberRingedToposMap F J O φ).comp
        ((fiberStageMorphism F J O n).comp
          (IsAugmentation.ringedHom F J K u0 O O_D aSharp)))
      ((fiberStageMorphism F J O m).comp
        (IsAugmentation.ringedHom F J K u0 O O_D aSharp)) where
  homIso := MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso _ _
    (fiberModulePullbackStageInverseImageIso F J K u0 O O_D aSharp φ)
  comm := by sorry

/-- Inverse-image form of `a_m ∘ f_φ = a_n` on modules. -/
def fiberModulePullbackStageCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ((fiberStageMorphism F J O m).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G ≅
      (fiberRingedToposMap F J O φ).modulePullback.obj
        (((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G) where
  hom :=
    (ToposHom.modulePullbackIsoOfTwoIso
      (fiberModulePullbackStageTwoIso F J K u0 O O_D aSharp φ)).inv.app G ≫
      (ToposHom.modulePullbackCompIso (fiberRingedToposMap F J O φ)
        ((fiberStageMorphism F J O n).comp
          (IsAugmentation.ringedHom F J K u0 O O_D aSharp))).hom.app G
  inv := fiberModulePullbackStageComp F J O
    (IsAugmentation.ringedHom F J K u0 O O_D aSharp) G φ
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Stage pullback comparisons for a ringed augmentation are invertible. -/
instance fiberModulePullbackStageComp_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (fiberModulePullbackStageComp F J O (IsAugmentation.ringedHom F J K u0 O O_D aSharp) G φ) :=
  (fiberModulePullbackStageCompIso F J K u0 O O_D aSharp G φ).isIso_inv

/-- The structure map `g_{m!}(a_m^* G) ⟶ g_{n!}(a_n^* G)` induced by a fiberwise simplex
operator `φ : n ⟶ m`. -/
def fiberLowerShriekModulePullback_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberModuleLowerShriek F J O m).obj
      (((fiberStageMorphism F J O m).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G) ⟶
    (fiberModuleLowerShriek F J O n).obj
      (((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G) :=
  ((fiberModuleLowerShriek.adjunction F J O m).homEquiv
      (((fiberStageMorphism F J O m).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G)
      ((fiberModuleLowerShriek F J O n).obj
        (((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G))).symm
    ((fiberModulePullbackStageCompIso F J K u0 O O_D aSharp G φ).hom ≫
      fiberModuleLowerShriek_component F J O φ
        (((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G) ≫
      (fiberModuleInverseImageIsoModulePullback F J O m).inv.app
        ((fiberModuleLowerShriek F J O n).obj
          (((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G)))

/-- Identity simplex operators induce identity structure maps. -/
theorem fiberLowerShriekModulePullback_map_id (n : SimplexCategory) :
    fiberLowerShriekModulePullback_map F J K u0 O O_D aSharp G (𝟙 n) =
      𝟙 ((fiberModuleLowerShriek F J O n).obj
        (((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!}(a_n^* G)` are functorial in fiberwise simplex operators. -/
theorem fiberLowerShriekModulePullback_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    fiberLowerShriekModulePullback_map F J K u0 O O_D aSharp G (ψ ≫ φ) =
      fiberLowerShriekModulePullback_map F J K u0 O O_D aSharp G φ ≫
        fiberLowerShriekModulePullback_map F J K u0 O O_D aSharp G ψ :=
  sorry

/-- The simplicial sheaf of `O`-modules `n ↦ g_{n!}(a_n^* G)` on the total fiberwise site. -/
def fiberLowerShriekModulePullback : SimplicialObject (SheafOfModules.{w} O) where
  obj n :=
    (fiberModuleLowerShriek F J O n.unop).obj
      (((fiberStageMorphism F J O n.unop).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G)
  map f := fiberLowerShriekModulePullback_map F J K u0 O O_D aSharp G f.unop
  map_id n := fiberLowerShriekModulePullback_map_id F J K u0 O O_D aSharp G n.unop
  map_comp f g := fiberLowerShriekModulePullback_map_comp F J K u0 O O_D aSharp G g.unop f.unop

/-- The value of `fiberLowerShriekModulePullback` at `n` is `g_{n!}(a_n^* G)`. -/
theorem fiberLowerShriekModulePullback_obj (n : SimplexCategory) :
    (fiberLowerShriekModulePullback F J K u0 O O_D aSharp G).obj (op n) =
      (fiberModuleLowerShriek F J O n).obj
        (((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G) :=
  rfl

/-- The face map `d_i : g_{(n+1)!}(a_{n+1}^* G) ⟶ g_{n!}(a_n^* G)`. -/
def fiberModulePullbackFace (n : ℕ) (i : Fin (n + 2)) :
    (fiberLowerShriekModulePullback F J K u0 O O_D aSharp G).obj (op ⦋n + 1⦌) ⟶
      (fiberLowerShriekModulePullback F J K u0 O O_D aSharp G).obj (op ⦋n⦌) :=
  (fiberLowerShriekModulePullback F J K u0 O O_D aSharp G).δ i


/-- The component of the fiberwise augmentation `g_{n!}(a_n^* G) ⟶ a^* G` at a simplex `n`. -/
def fiberModulePullbackAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (fiberLowerShriekModulePullback F J K u0 O O_D aSharp G).obj n ⟶ (IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G :=
  ((fiberModuleLowerShriek.adjunction F J O n.unop).homEquiv
      (((fiberStageMorphism F J O n.unop).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G)
      ((IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G)).symm
    ((ToposHom.modulePullbackCompIso (fiberStageMorphism F J O n.unop) (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).hom.app G ≫
      (fiberModuleInverseImageIsoModulePullback F J O n.unop).inv.app
        ((IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G))

/-- Naturality of the degreewise fiberwise augmentation `g_{n!}(a_n^* G) ⟶ a^* G`. -/
theorem fiberModulePullbackAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (fiberLowerShriekModulePullback F J K u0 O O_D aSharp G).map f ≫
          fiberModulePullbackAugmented_hom_app F J K u0 O O_D aSharp G m =
        fiberModulePullbackAugmented_hom_app F J K u0 O O_D aSharp G n ≫
          ((SimplicialObject.const _).obj ((IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G)).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!}(a_n^* G) ⟶ const (a^* G)`. -/
def fiberModulePullbackAugmented_hom :
    fiberLowerShriekModulePullback F J K u0 O O_D aSharp G ⟶
      (SimplicialObject.const _).obj ((IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G) where
  app := fiberModulePullbackAugmented_hom_app F J K u0 O O_D aSharp G
  naturality := fiberModulePullbackAugmented_hom_naturality F J K u0 O O_D aSharp G

/-- The augmented simplicial object of `g_{n!}(a_n^* G)` over `a^* G`. -/
def fiberModulePullbackAugmented : SimplicialObject.Augmented (SheafOfModules.{w} O) where
  left := fiberLowerShriekModulePullback F J K u0 O O_D aSharp G
  right := (IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G
  hom := fiberModulePullbackAugmented_hom F J K u0 O O_D aSharp G

/-- The alternating-face chain complex
`… → g_{2!}(a_2^* G) → g_{1!}(a_1^* G) → g_{0!}(a_0^* G)`. -/
abbrev fiberModulePullbackComplex : ChainComplex (SheafOfModules.{w} O) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (fiberModulePullbackAugmented F J K u0 O O_D aSharp G))

/-- Degree `n` of `fiberModulePullbackComplex` is the sheaf of modules `g_{n!}(a_n^* G)`. -/
theorem fiberModulePullbackComplex_X (n : ℕ) :
    (fiberModulePullbackComplex F J K u0 O O_D aSharp G).X n =
      (fiberModuleLowerShriek F J O ⦋n⦌).obj
        (((fiberStageMorphism F J O ⦋n⦌).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePullback.obj G) :=
  rfl

/-- Differentials of `fiberModulePullbackComplex` are the alternating sums of face maps. -/
theorem fiberModulePullbackComplex_d_eq (n : ℕ) :
    (fiberModulePullbackComplex F J K u0 O O_D aSharp G).d (n + 1) n =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • fiberModulePullbackFace F J K u0 O O_D aSharp G n i := by
    exact alternatingFaceMapComplex_obj_d _ n

/-- The canonical chain-map augmentation from `fiberModulePullbackComplex` to `a^* G`
concentrated in degree zero. -/
def fiberModulePullbackAugmentation :
    fiberModulePullbackComplex F J K u0 O O_D aSharp G ⟶
      (ChainComplex.single₀ _).obj ((IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G) :=
  AlternatingFaceMapComplex.ε.app (fiberModulePullbackAugmented F J K u0 O O_D aSharp G)

/-- The degree-zero component of `fiberModulePullbackAugmentation` is the simplicial
augmentation at `⦋0⦌`. -/
theorem fiberModulePullbackAugmentation_f_zero :
    (fiberModulePullbackAugmentation F J K u0 O O_D aSharp G).f 0 =
      (fiberModulePullbackAugmented F J K u0 O O_D aSharp G).hom.app (op ⦋0⦌) :=
  AlternatingFaceMapComplex.ε_app_f_zero _

/-- The canonical alternating-face augmentation of the module inverse image along a
site augmentation is a quasi-isomorphism. -/
instance fiberModulePullbackAugmentation_quasiIso :
    QuasiIso
      (fiberModulePullbackAugmentation F J K u0 O O_D aSharp G :
        fiberModulePullbackComplex F J K u0 O O_D aSharp G ⟶
          (ChainComplex.single₀ _).obj ((IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G)) :=
  sorry

end CategoryTheory.Grothendieck
