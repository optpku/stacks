/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import stacks_project.Chap85.Lemma_85_3_5

/-!
# Ringed fiber inclusions of a simplicial object of sites

Case B of Situation 85.3.3: the ringed topos morphisms `g_n` and `f_φ` along fiber
inclusions, module lower shriek, and the componentwise coproduct formula.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite
open Sheaf.InternalModule

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})

/-- The total ringed site `(Sh(C_total), O)` in case B. -/
abbrev fiberTotalRingedSite : RingedSite.{u, v, w} :=
  ofRingSheaf (topology F J) O

/-- The structure sheaf of `fiberTotalRingedSite F J O` is `O`. -/
theorem fiberTotalRingedSite_structureSheaf :
    (fiberTotalRingedSite F J O).structureSheaf = O :=
  sorry

/-- The ring sheaf `O_n` on the degree-`n` fiber, the continuous inverse image of `O`
along `ι F (op n)`. -/
abbrev fiberComponentRingSheaf (n : SimplexCategory) :
    Sheaf (J (op n)).toGrothendieck RingCat.{w} :=
  Cocontinuous.inverseImageRingSheaf (ι F (op n)) O

/-- `fiberComponentRingSheaf` is inverse image of `O` along `ι F (op n)`. -/
theorem fiberComponentRingSheaf_eq (n : SimplexCategory) :
    fiberComponentRingSheaf F J O n = Cocontinuous.inverseImageRingSheaf (ι F (op n)) O :=
  sorry

/-- The degree-`n` ringed site `(Sh(C_n), O_n)` in case B. -/
abbrev fiberComponentRingedSite (n : SimplexCategory) : RingedSite.{u, v, w} :=
  ofRingSheaf (J (op n)).toGrothendieck (fiberComponentRingSheaf F J O n)

/-- The structure sheaf of `fiberComponentRingedSite F J O n` is `O_n`. -/
theorem fiberComponentRingedSite_structureSheaf (n : SimplexCategory) :
    (fiberComponentRingedSite F J O n).structureSheaf = fiberComponentRingSheaf F J O n :=
  sorry

variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- The identity comparison along `ι F (op n)` from which the structure map of `g_n` is
obtained, so `g_n⁻¹ O = O_n`. -/
def fiberStageIdentityComparison (n : SimplexCategory) :
    (ι F (op n)).op ⋙ (fiberTotalRingedSite F J O).structureSheaf.obj ⟶
      (fiberComponentRingedSite F J O n).structureSheaf.obj :=
  𝟙 ((ι F (op n)).op ⋙ O.obj)

/-- `fiberStageIdentityComparison` is the identity on the restricted structure sheaf. -/
theorem fiberStageIdentityComparison_eq_id (n : SimplexCategory) :
    fiberStageIdentityComparison F J O n = 𝟙 ((ι F (op n)).op ⋙ O.obj) :=
  sorry

/-- The morphism of ringed topoi `g_n : (Sh(C_n), O_n) ⟶ (Sh(C_total), O)` induced by
the fiber inclusion `ι F (op n)`. -/
def fiberStageMorphism (n : SimplexCategory) :
    ToposHom (fiberComponentRingedSite F J O n) (fiberTotalRingedSite F J O) :=
  @Cocontinuous.toRingedTopos.{u, v, u, v, w}
    (fiberComponentRingedSite F J O n) (fiberTotalRingedSite F J O) (ι F (op n))
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fiberStageIdentityComparison F J O n)

/-- The underlying topos morphism of `fiberStageMorphism F J O n` is `fiberMorphism F J n`. -/
theorem fiberStageMorphism_toTopos (n : SimplexCategory) :
    (fiberStageMorphism F J O n).toTopos = fiberMorphism F J n :=
  sorry

/-- Presheaf form of `O(φ)` along a simplex operator in case B. -/
def fiberRingedToposMapComparison {m n : SimplexCategory} (φ : m ⟶ n) :
    (F.map φ.op).toFunctor.op ⋙ (fiberComponentRingedSite F J O m).structureSheaf.obj ⟶
      (fiberComponentRingedSite F J O n).structureSheaf.obj :=
  whiskerRight (NatTrans.op (ιNatTrans φ.op)) O.obj

/-- `fiberRingedToposMapComparison` is whiskering of `ιNatTrans` with `O`. -/
theorem fiberRingedToposMapComparison_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    fiberRingedToposMapComparison F J O φ =
      whiskerRight (NatTrans.op (ιNatTrans φ.op)) O.obj :=
  sorry

/-- The morphism of ringed topoi `f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)` in case B, with
structure map `O(φ) : f_φ⁻¹ O_m ⟶ O_n`. -/
def fiberRingedToposMap {m n : SimplexCategory} (φ : m ⟶ n) :
    ToposHom (fiberComponentRingedSite F J O n) (fiberComponentRingedSite F J O m) :=
  @Cocontinuous.toRingedTopos.{u, v, u, v, w}
    (fiberComponentRingedSite F J O n) (fiberComponentRingedSite F J O m)
    (F.map φ.op).toFunctor
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fiberRingedToposMapComparison F J O φ)

/-- The underlying topos morphism of `fiberRingedToposMap F J O φ` is `toposMap F J φ`. -/
theorem fiberRingedToposMap_toTopos {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberRingedToposMap F J O φ).toTopos = toposMap F J φ :=
  sorry

/-- Module lower shriek `g_{n!}` along the degree-`n` fiber inclusion. -/
abbrev fiberModuleLowerShriek (n : SimplexCategory) :
    SheafOfModules.{w} (fiberComponentRingSheaf F J O n) ⥤ SheafOfModules.{w} O :=
  Cocontinuous.moduleLowerShriek (ι F (op n)) O

/-- `fiberModuleLowerShriek` is the ReasLib lower shriek along `ι F (op n)`. -/
theorem fiberModuleLowerShriek_eq (n : SimplexCategory) :
    fiberModuleLowerShriek F J O n = Cocontinuous.moduleLowerShriek (ι F (op n)) O :=
  sorry

/-- The canonical adjunction `g_{n!} ⊣` module inverse image along `ι F (op n)`. -/
def fiberModuleLowerShriek.adjunction (n : SimplexCategory) :
    fiberModuleLowerShriek F J O n ⊣ Cocontinuous.moduleInverseImage (ι F (op n)) O :=
  Cocontinuous.moduleLowerShriek.adjunction (ι F (op n)) O

/-- The adjunction is the ReasLib lower-shriek/inverse-image adjunction along `ι`. -/
theorem fiberModuleLowerShriek.adjunction_eq (n : SimplexCategory) :
    fiberModuleLowerShriek.adjunction F J O n =
      Cocontinuous.moduleLowerShriek.adjunction (ι F (op n)) O :=
  sorry

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]

/-- Underlying type-valued sheaf of module inverse image along `ι F (op n)`. -/
def fiberModuleInverseImage_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      ((Cocontinuous.moduleInverseImage (ι F (op n)) O).obj M) ≅
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  (fullyFaithfulSheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Restriction of scalars along the structure map of `g_n` does not change the
underlying type-valued sheaf of `g_n^* M` in case B. -/
def fiberModulePullback_restrictScalars_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      ((fiberStageMorphism F J O n).modulePullback.obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying
          ((fiberStageMorphism F J O n).toTopos.ringInverseImage.obj O)).obj
        ((SheafOfModules.restrictScalars (fiberStageMorphism F J O n).structureMap).obj
          ((fiberStageMorphism F J O n).modulePullback.obj M)) :=
  (fullyFaithfulSheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- The scalar-extension unit comparing geometric inverse image with `g_n^*` in case B. -/
def fiberModulePullback_scalarUnit (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    ((fiberStageMorphism F J O n).toTopos.moduleInverseImage O).obj M ⟶
      (SheafOfModules.restrictScalars (fiberStageMorphism F J O n).structureMap).obj
        ((fiberStageMorphism F J O n).modulePullback.obj M) :=
  (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
      (fiberStageMorphism F J O n).structureMap).unit.app
    (((fiberStageMorphism F J O n).toTopos.moduleInverseImage O).obj M)

/-- The scalar-extension unit is an isomorphism in case B. -/
instance fiberModulePullback_scalarUnit_isIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    IsIso (fiberModulePullback_scalarUnit F J O n M) :=
  sorry

/-- The cocontinuous-to-continuous comparison along `ι F (op n)` is an isomorphism. -/
instance fiber_cocontinuousPullback_comparison_isIso (n : SimplexCategory) :
    IsIso (Functor.CocontinuousPullback.comparison (ι F (op n))
      (J (op n)).toGrothendieck (topology F J)) :=
  Functor.CocontinuousPullback.comparison.isIso (ι F (op n))
    (J (op n)).toGrothendieck (topology F J)

/-- Underlying type-valued sheaf of `g_n^*` in case B. -/
def fiberModulePullback_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} O) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
      ((fiberStageMorphism F J O n).modulePullback.obj M) ≅
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  fiberModulePullback_restrictScalars_underlyingIso F J O n M ≪≫
    (asIso
      ((Sheaf.InternalModule.ToInternal.underlying
          ((fiberStageMorphism F J O n).toTopos.ringInverseImage.obj O)).map
        (fiberModulePullback_scalarUnit F J O n M))).symm ≪≫
    ((fiberStageMorphism F J O n).toTopos.moduleInverseImageForgetIso O).app M ≪≫
    (asIso
      (Functor.CocontinuousPullback.comparison (ι F (op n))
        (J (op n)).toGrothendieck (topology F J))).app
      ((Sheaf.InternalModule.ToInternal.underlying O).obj M)

/-- The comparison `g_n^* ⟶` module inverse image in case B, lifting
`CocontinuousPullback.comparison`. -/
def fiberModulePullbackToModuleInverseImage (n : SimplexCategory) :
    (fiberStageMorphism F J O n).modulePullback ⟶
      Cocontinuous.moduleInverseImage (ι F (op n)) O where
  app M :=
    Sheaf.InternalModule.homOfUnderlying (fiberComponentRingSheaf F J O n)
      ((fiberModulePullback_underlyingIso F J O n M).hom ≫
        (fiberModuleInverseImage_underlyingIso F J O n M).inv)
      sorry sorry
  naturality := sorry

/-- The comparison `fiberModulePullbackToModuleInverseImage` is an isomorphism. -/
instance fiberModulePullbackToModuleInverseImage_isIso (n : SimplexCategory) :
    IsIso (fiberModulePullbackToModuleInverseImage F J O n) :=
  sorry

/-- Module inverse image along `ι F (op n)` is isomorphic to `g_n^*` in case B. -/
def fiberModuleInverseImageIsoModulePullback (n : SimplexCategory) :
    Cocontinuous.moduleInverseImage (ι F (op n)) O ≅
      (fiberStageMorphism F J O n).modulePullback :=
  (asIso (fiberModulePullbackToModuleInverseImage F J O n)).symm

/-- The forward map of `fiberModuleInverseImageIsoModulePullback` is the inverse of the
cocontinuous-to-continuous comparison lift. -/
theorem fiberModuleInverseImageIsoModulePullback_hom (n : SimplexCategory) :
    (fiberModuleInverseImageIsoModulePullback F J O n).hom =
      (asIso (fiberModulePullbackToModuleInverseImage F J O n)).inv :=
  sorry

/-- Restriction of scalars along `O(φ)` does not change the underlying type-valued sheaf. -/
def fiberRingedToposMap_restrictScalars_forgetIso {m n : SimplexCategory} (φ : m ⟶ n)
    (N : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (Sheaf.InternalModule.ToInternal.underlying
        ((fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
          (fiberComponentRingSheaf F J O m))).obj
      ((SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj N) ≅
      (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj N :=
  (fullyFaithfulSheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).preimageIso <|
    NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- The forward and reverse comparisons of `fiberRingedToposMap_restrictScalars_forgetIso`
are inverse. -/
theorem fiberRingedToposMap_restrictScalars_forgetIso_hom_inv_id {m n : SimplexCategory}
    (φ : m ⟶ n) (N : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (fiberRingedToposMap_restrictScalars_forgetIso F J O φ N).hom ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ N).inv =
    𝟙 _ :=
  sorry

/-- The `ιNatTrans` 2-cell on underlying type-valued sheaves. -/
def fiberModuleLowerShriek_component_underlying {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj
      ((Sheaf.InternalModule.ToInternal.underlying
          (fiberComponentRingSheaf F J O n)).obj G) ⟶
      ((ι F (op m)).sheafPushforwardContinuous (Type w)
        (J (op m)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          ((fiberModuleLowerShriek F J O n).obj G)) :=
  (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerLeft (F.map φ.op).toFunctor.op
        ((sheafToPresheaf ((J (op n)).toGrothendieck) (Type w)).map
          ((Sheaf.InternalModule.ToInternal.underlying
              (fiberComponentRingSheaf F J O n)).map
            ((fiberModuleLowerShriek.adjunction F J O n).unit.app G) ≫
            (fiberModuleInverseImage_underlyingIso F J O n
              ((fiberModuleLowerShriek F J O n).obj G)).hom))) ≫
    (presheafToSheaf ((J (op m)).toGrothendieck) (Type w)).map
      (whiskerRight (NatTrans.op (ιNatTrans φ.op))
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          ((fiberModuleLowerShriek F J O n).obj G)).obj) ≫
    (sheafificationAdjunction ((J (op m)).toGrothendieck) (Type w)).counit.app
      (((ι F (op m)).sheafPushforwardContinuous (Type w)
          (J (op m)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj
          ((fiberModuleLowerShriek F J O n).obj G)))

/-- Geometric inverse-image form of the component map, before extending scalars along `O(φ)`. -/
def fiberModuleLowerShriek_component_geometric {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
        (fiberComponentRingSheaf F J O n)).obj G ⟶
      (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj
        ((Cocontinuous.moduleInverseImage (ι F (op m)) O).obj
          ((fiberModuleLowerShriek F J O n).obj G)) :=
  Sheaf.InternalModule.homOfUnderlying
    ((fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
      (fiberComponentRingSheaf F J O n))
    (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImageForgetIso
        (fiberComponentRingSheaf F J O n)).hom.app G ≫
      fiberModuleLowerShriek_component_underlying F J O φ G ≫
      (fiberModuleInverseImage_underlyingIso F J O m
        ((fiberModuleLowerShriek F J O n).obj G)).inv ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ
        ((Cocontinuous.moduleInverseImage (ι F (op m)) O).obj
          ((fiberModuleLowerShriek F J O n).obj G))).inv)
    sorry sorry

/-- The canonical component map `f_φ^* G ⟶ (g_{n!} G)_m` in case B, using the lower-shriek
unit and the mate of `ιNatTrans`, then extending scalars along `O(φ)`. -/
def fiberModuleLowerShriek_component {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (fiberRingedToposMap F J O φ).modulePullback.obj G ⟶
      (fiberStageMorphism F J O m).modulePullback.obj
        ((fiberModuleLowerShriek F J O n).obj G) :=
  (ToposHom.ModulePullback.scalarHomEquiv (fiberRingedToposMap F J O φ)
      (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
          (fiberComponentRingSheaf F J O n)).obj G)
      ((fiberStageMorphism F J O m).modulePullback.obj
        ((fiberModuleLowerShriek F J O n).obj G))).symm
    (fiberModuleLowerShriek_component_geometric F J O φ G ≫
      (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).map
        ((fiberModuleInverseImageIsoModulePullback F J O m).hom.app
          ((fiberModuleLowerShriek F J O n).obj G)))

/-- The component map is the scalar-extension adjunct of the geometric `ιNatTrans` mate,
transported along `fiberModuleInverseImageIsoModulePullback`. -/
theorem fiberModuleLowerShriek_component_adjunct {n m : SimplexCategory} (φ : n ⟶ m)
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (ToposHom.ModulePullback.scalarHomEquiv (fiberRingedToposMap F J O φ)
        (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
            (fiberComponentRingSheaf F J O n)).obj G)
        ((fiberStageMorphism F J O m).modulePullback.obj
          ((fiberModuleLowerShriek F J O n).obj G)))
      (fiberModuleLowerShriek_component F J O φ G) =
      fiberModuleLowerShriek_component_geometric F J O φ G ≫
        (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).map
          ((fiberModuleInverseImageIsoModulePullback F J O m).hom.app
            ((fiberModuleLowerShriek F J O n).obj G)) :=
  sorry

/-- The coproduct comparison morphism in case B. -/
def fiberModuleLowerShriek_componentBiproductHom (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (∐ fun φ : n ⟶ m ↦ (fiberRingedToposMap F J O φ).modulePullback.obj G) ⟶
      (fiberStageMorphism F J O m).modulePullback.obj
        ((fiberModuleLowerShriek F J O n).obj G) :=
  Sigma.desc fun φ ↦ fiberModuleLowerShriek_component F J O φ G

/-- The case B coproduct comparison is the coproduct of the component maps. -/
theorem fiberModuleLowerShriek_componentBiproductHom_eq (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    fiberModuleLowerShriek_componentBiproductHom F J O n m G =
      Sigma.desc fun φ ↦ fiberModuleLowerShriek_component F J O φ G :=
  sorry

/-- The case B coproduct comparison morphism is an isomorphism. -/
instance fiberModuleLowerShriek_componentBiproductHom_isIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    IsIso (fiberModuleLowerShriek_componentBiproductHom F J O n m G) :=
  sorry

/-- Restriction of `g_{n!} G` to `C_m` is `⊕_{φ : n ⟶ m} f_φ^* G` in case B. -/
def fiberModuleLowerShriek_componentBiproductIso (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) :
    (∐ fun φ : n ⟶ m ↦ (fiberRingedToposMap F J O φ).modulePullback.obj G) ≅
      (fiberStageMorphism F J O m).modulePullback.obj
        ((fiberModuleLowerShriek F J O n).obj G) :=
  asIso (fiberModuleLowerShriek_componentBiproductHom F J O n m G)

/-- The coproduct inclusion of `f_φ^* G` followed by the comparison is the component map. -/
theorem fiberModuleLowerShriek_componentBiproduct_ι (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O m))]
    (G : SheafOfModules.{w} (fiberComponentRingSheaf F J O n)) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m ↦
        (fiberRingedToposMap F J O ψ).modulePullback.obj G) φ ≫
      (fiberModuleLowerShriek_componentBiproductIso F J O n m G).hom =
      fiberModuleLowerShriek_component F J O φ G :=
  sorry

end CategoryTheory.Grothendieck
