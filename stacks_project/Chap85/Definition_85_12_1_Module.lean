module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap85.Definition_85_12_1_Component

/-!
# Module and derived comparisons on a ringed simplicial site

Restriction of `O`-modules and of objects of `D(O)` and `D(C_total)` to stages,
together with the simplex-operator maps `f_φ^* F_m ⟶ F_n` and `Lf_φ^* K_m ⟶ K_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open RingedSite
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Canonical derived-category structure on modules over the total ringed site. -/
instance total_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :=
  instHasDerivedCategory_moduleCat (totalRingedSite C J O)

/-- Canonical derived-category structure on modules over a component ringed site. -/
instance component_hasDerivedCategory (n : SimplexCategory) :
    HasDerivedCategory
      (SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) :=
  instHasDerivedCategory_moduleCat (componentRingedSite C J O n)

/-- Restriction of an `O`-module on `C_total` to the degree-`n` site, i.e. `F_n = g_n^* F`. -/
def moduleComponent (n : SimplexCategory) :
    SheafOfModules.{w} (totalRingedSite C J O).structureSheaf ⥤
      SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf :=
  (stageMorphism C J O n).modulePullback

/-- `moduleComponent n` is module pullback along the stage inclusion `g_n`. -/
theorem moduleComponent_eq (n : SimplexCategory) :
    moduleComponent C J O n = (stageMorphism C J O n).modulePullback :=
  sorry

/-- Restriction of an object of `D(O)` to the degree-`n` site, i.e. `K_n = Lg_n^* K`. -/
def moduleDerivedComponent (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (totalRingedSite C J O) ⥤
      Hom.ModuleDerived.{w} (componentRingedSite C J O n) :=
  (stageMorphism C J O n).modulePullbackDerived

/-- `moduleDerivedComponent n` is derived module pullback along `g_n`. -/
theorem moduleDerivedComponent_eq (n : SimplexCategory) :
    moduleDerivedComponent C J O n = (stageMorphism C J O n).modulePullbackDerived :=
  sorry

/-- Cocontinuous pullback along `ofStage n` is isomorphic to continuous pushforward. -/
def ofStage_cocontinuousContinuousIso (n : SimplexCategory) :
    (ofStage C n).sheafPullbackCocontinuous (Type w)
        (J n).toGrothendieck (topology C J) ≅
      (ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J) :=
  NatIso.ofComponents
    (fun F ↦
      { hom :=
          CocontinuousPullback.comparisonApp (ofStage C n)
            (J n).toGrothendieck (topology C J) F
        inv :=
          ((ofStage C n).sheafPushforwardContinuous (Type w)
              (J n).toGrothendieck (topology C J)).map
            (sheafificationIso F).hom ≫
            ((ofStage C n).pushforwardContinuousSheafificationCompatibility (Type w)
                (J n).toGrothendieck (topology C J)).inv.app F.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Underlying type-valued sheaves identify geometric inverse image along `g_n` with
restriction of the underlying sheaf of `F` along `ofStage C n`. -/
def moduleInverseImage_underlyingIso
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) :
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageMorphism C J O n).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf)).obj
      (((stageMorphism C J O n).toTopos.moduleInverseImage
          (totalRingedSite C J O).structureSheaf).obj F) ≅
    (component C J (Type w) n).obj
      ((Sheaf.InternalModule.ToInternal.underlying
          (totalRingedSite C J O).structureSheaf).obj F) :=
  ((stageMorphism C J O n).toTopos.moduleInverseImageForgetIso
      (totalRingedSite C J O).structureSheaf).app F ≪≫
    (ofStage_cocontinuousContinuousIso C J n).app
      ((Sheaf.InternalModule.ToInternal.underlying
          (totalRingedSite C J O).structureSheaf).obj F)

/-- Restriction of scalars does not change the underlying type-valued sheaf. -/
def restrictScalars_underlyingIso (n : SimplexCategory)
    {R R' : Sheaf ((J n).toGrothendieck) RingCat.{w}} (α : R ⟶ R') :
    SheafOfModules.restrictScalars.{w} α ⋙
        Sheaf.InternalModule.ToInternal.underlying R ≅
      Sheaf.InternalModule.ToInternal.underlying R' :=
  Iso.refl _

/-- Geometric inverse image of an `O`-module along the stage inclusion `g_n`. -/
def moduleInverseImageComponent (n : SimplexCategory) :
    SheafOfModules.{w} (totalRingedSite C J O).structureSheaf ⥤
      SheafOfModules.{w}
        ((stageMorphism C J O n).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf) :=
  (stageMorphism C J O n).toTopos.moduleInverseImage
    (totalRingedSite C J O).structureSheaf

/-- Underlying type-valued comparison of `moduleTransitionDirect`, as a map of sheaves of types
on `C_m`. -/
def moduleTransitionDirect_underlying {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageMorphism C J O m).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf)).obj
      ((moduleInverseImageComponent C J O m).obj F) ⟶
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageMorphism C J O m).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf)).obj
      ((SheafOfModules.restrictScalars.{w}
          (stageMorphism C J O m).structureMap).obj
        ((ringedToposMap C J O φ).modulePushforward.obj
          ((moduleComponent C J O n).obj F))) :=
  (moduleInverseImage_underlyingIso C J O F m).hom ≫
    transitionDirect C J (Type w) φ
      ((Sheaf.InternalModule.ToInternal.underlying
          (totalRingedSite C J O).structureSheaf).obj F) ≫
      ((C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
          (J m).toGrothendieck (J n).toGrothendieck).map
        ((moduleInverseImage_underlyingIso C J O F n).inv ≫
          (Sheaf.InternalModule.ToInternal.underlying
              ((stageMorphism C J O n).toTopos.ringInverseImage.obj
                (totalRingedSite C J O).structureSheaf)).map
            ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
                (stageMorphism C J O n).structureMap).unit.app
              ((moduleInverseImageComponent C J O n).obj F))) ≫
      (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ)).inv.app
        ((moduleComponent C J O n).obj F) ≫
      (restrictScalars_underlyingIso C J m
          (stageMorphism C J O m).structureMap).inv.app
        ((ringedToposMap C J O φ).modulePushforward.obj
          ((moduleComponent C J O n).obj F))

/-- Geometric module comparison `g_m⁻¹ F ⟶ (f_φ)_* F_n` over the inverse-image ring of `g_m`. -/
def moduleTransitionDirect_geom {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    (moduleInverseImageComponent C J O m).obj F ⟶
      (SheafOfModules.restrictScalars.{w}
          (stageMorphism C J O m).structureMap).obj
        ((ringedToposMap C J O φ).modulePushforward.obj
          ((moduleComponent C J O n).obj F)) :=
  Sheaf.InternalModule.homOfUnderlying
    ((stageMorphism C J O m).toTopos.ringInverseImage.obj
      (totalRingedSite C J O).structureSheaf)
    (moduleTransitionDirect_underlying C J O φ F) sorry sorry

/-- Direct-image comparison `F_m ⟶ (f_φ)_* F_n` of `O`-modules, obtained by extending scalars
along the stage structure map and applying the scalar-extension counit. -/
def moduleTransitionDirect {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    (moduleComponent C J O m).obj F ⟶
      (ringedToposMap C J O φ).modulePushforward.obj ((moduleComponent C J O n).obj F) :=
  (SheafOfModules.ChangeOfRings.extendScalars
        (stageMorphism C J O m).structureMap).map
      (moduleTransitionDirect_geom C J O φ F) ≫
    (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (stageMorphism C J O m).structureMap).counit.app
      ((ringedToposMap C J O φ).modulePushforward.obj ((moduleComponent C J O n).obj F))

/-- The source comparison `F(φ) : f_φ^* F_m ⟶ F_n` of `O`-modules. -/
def moduleTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    (ringedToposMap C J O φ).modulePullback.obj ((moduleComponent C J O m).obj F) ⟶
      (moduleComponent C J O n).obj F :=
  ((ringedToposMap C J O φ).moduleAdjunction.homEquiv
      ((moduleComponent C J O m).obj F) ((moduleComponent C J O n).obj F)).symm
    (moduleTransitionDirect C J O φ F)

/-- The adjunction mate of `moduleTransition` is `moduleTransitionDirect`. -/
theorem moduleTransition_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    ((ringedToposMap C J O φ).moduleAdjunction.homEquiv
        ((moduleComponent C J O m).obj F) ((moduleComponent C J O n).obj F))
      (moduleTransition C J O φ F) =
    moduleTransitionDirect C J O φ F :=
  sorry

/-- The module comparison `F(φ)` as a natural transformation in `F`. -/
def moduleTransitionNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    moduleComponent C J O m ⋙ (ringedToposMap C J O φ).modulePullback ⟶
      moduleComponent C J O n where
  app F := moduleTransition C J O φ F
  naturality := sorry

/-- Module pullback along a stage inclusion is additive. -/
instance stageMorphism_modulePullback_additive (n : SimplexCategory) :
    (stageMorphism C J O n).modulePullback.Additive :=
  sorry

/-- Stage restriction of `O`-modules is additive. -/
instance moduleComponent_additive (n : SimplexCategory) :
    (moduleComponent C J O n).Additive :=
  stageMorphism_modulePullback_additive C J O n

/-- The composite module pullback `g_m^*` then `f_φ^*` is additive. -/
instance moduleComposite_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    ((stageMorphism C J O m).modulePullback ⋙
      (ringedToposMap C J O φ).modulePullback).Additive :=
  sorry

/-- The composite `moduleComponent m ⋙ (ringedToposMap φ).modulePullback` is additive. -/
instance moduleComponent_comp_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    (moduleComponent C J O m ⋙ (ringedToposMap C J O φ).modulePullback).Additive :=
  sorry

/-- Homotopy-to-derived of module pullback along `ringedToposMap φ` has a total left derived
functor. -/
instance ringedToposMap_toDerived_hasLeftDerived {m n : SimplexCategory} (φ : m ⟶ n) :
    (Functor.Homotopy.toDerived (ringedToposMap C J O φ).modulePullback).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (componentRingedSite C J O m).structureSheaf) (up ℤ)) :=
  sorry

/-- Homotopy-to-derived of module pullback along `g_n` has a total left derived functor. -/
instance stageMorphism_toDerived_hasLeftDerived (n : SimplexCategory) :
    (Functor.Homotopy.toDerived (stageMorphism C J O n).modulePullback).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) (up ℤ)) :=
  sorry

/-- Homotopy-to-derived of the composite module pullback `g_m^*` then `f_φ^*` has a total
left derived functor. -/
instance moduleComposite_hasLeftDerived {m n : SimplexCategory} (φ : m ⟶ n) :
    (Functor.Homotopy.toDerived
        ((stageMorphism C J O m).modulePullback ⋙
          (ringedToposMap C J O φ).modulePullback)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) (up ℤ)) :=
  sorry

/-- Homotopy-to-derived natural transformation induced by `moduleTransitionNatTrans`. -/
def moduleTransitionToDerived {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.Homotopy.toDerived
        ((stageMorphism C J O m).modulePullback ⋙
          (ringedToposMap C J O φ).modulePullback) ⟶
      Functor.Homotopy.toDerived (stageMorphism C J O n).modulePullback :=
  Functor.whiskerRight
    (NatTrans.mapHomotopyCategory (moduleTransitionNatTrans C J O φ) (up ℤ))
    DerivedCategory.Qh

/-- The derived comparison `Lf_φ^* K_m ⟶ K_n` of objects of `D(O)`. -/
def moduleDerivedTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    (ringedToposMap C J O φ).modulePullbackDerived.obj
        ((moduleDerivedComponent C J O m).obj K) ⟶
      (moduleDerivedComponent C J O n).obj K :=
  (Functor.LeftDerived.Homotopy.Composition.comparison
        (ringedToposMap C J O φ).modulePullback
        (stageMorphism C J O m).modulePullback
        ((stageMorphism C J O m).modulePullback ⋙
          (ringedToposMap C J O φ).modulePullback)
        (Iso.refl _) ≫
      Functor.LeftDerived.mapNatTrans DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) (up ℤ))
        (moduleTransitionToDerived C J O φ)).app K

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Stage restriction of abelian sheaves is additive. -/
instance component_abelian_additive (n : SimplexCategory) :
    (component C J AddCommGrpCat.{w} n).Additive :=
  sorry

/-- Stage restriction of abelian sheaves preserves finite limits. -/
instance component_abelian_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (component C J AddCommGrpCat.{w} n) :=
  sorry

/-- Stage restriction of abelian sheaves preserves finite colimits. -/
instance component_abelian_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (component C J AddCommGrpCat.{w} n) :=
  sorry

/-- Pullback of abelian sheaves along a simplex operator is additive. -/
instance toFunctor_abelian_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
      (J m).toGrothendieck (J n).toGrothendieck).Additive :=
  sorry

/-- Pullback of abelian sheaves along a simplex operator preserves finite limits. -/
instance toFunctor_abelian_preservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits
      ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck) :=
  sorry

/-- Pullback of abelian sheaves along a simplex operator preserves finite colimits. -/
instance toFunctor_abelian_preservesFiniteColimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteColimits
      ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck) :=
  sorry

/-- The natural transformation of abelian stage restriction whose components are `F(φ)`. -/
def abelianTransitionNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    component C J AddCommGrpCat.{w} m ⋙
      (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck ⟶
    component C J AddCommGrpCat.{w} n where
  app F := abelianTransition C J φ F
  naturality := sorry

/-- Restriction of an object of `D(C_total)` to the degree-`n` site. -/
def derivedComponent (n : SimplexCategory) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :=
  (component C J AddCommGrpCat.{w} n).mapDerivedCategory

/-- `derivedComponent n` is `mapDerivedCategory` of abelian stage restriction. -/
theorem derivedComponent_eq (n : SimplexCategory) :
    derivedComponent C J n = (component C J AddCommGrpCat.{w} n).mapDerivedCategory :=
  sorry

/-- Bundled exact stage restriction of abelian sheaves. -/
def derivedComponentExact (n : SimplexCategory) :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤ₑ
      Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} :=
  ExactFunctor.of (component C J AddCommGrpCat.{w} n)

/-- The underlying functor of `derivedComponentExact n` is abelian stage restriction. -/
theorem derivedComponentExact_obj (n : SimplexCategory) :
    (derivedComponentExact C J n).obj = component C J AddCommGrpCat.{w} n :=
  sorry

/-- Bundled exact inverse image of abelian sheaves along a simplex operator. -/
def abelianInverseImageExact {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w} ⥤ₑ
      Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} :=
  ExactFunctor.of
    ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
      (J m).toGrothendieck (J n).toGrothendieck)

/-- The underlying functor of `abelianInverseImageExact φ` is `f_φ⁻¹`. -/
theorem abelianInverseImageExact_obj {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianInverseImageExact C J φ).obj = abelianInverseImage C J φ :=
  sorry

/-- Inverse image of abelian sheaves along a simplex operator is additive. -/
instance abelianInverseImage_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianInverseImage C J φ).Additive :=
  toFunctor_abelian_additive C J φ

/-- Inverse image of abelian sheaves along a simplex operator preserves finite limits. -/
instance abelianInverseImage_preservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits (abelianInverseImage C J φ) :=
  toFunctor_abelian_preservesFiniteLimits C J φ

/-- Inverse image of abelian sheaves along a simplex operator preserves finite colimits. -/
instance abelianInverseImage_preservesFiniteColimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteColimits (abelianInverseImage C J φ) :=
  toFunctor_abelian_preservesFiniteColimits C J φ

/-- Exactness identifies `D(component m ⋙ f_φ⁻¹)` with `f_φ⁻¹` after `K ↦ K_m`. -/
def derivedTransitionCompIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (component C J AddCommGrpCat.{w} m ⋙
        (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
          (J m).toGrothendieck (J n).toGrothendieck).mapDerivedCategory ≅
      (derivedComponent C J m) ⋙ (abelianInverseImage C J φ).mapDerivedCategory :=
  CategoryTheory.ExactFunctor.MapDerivedCategory.compFunctorIso
    (derivedComponentExact C J m) (abelianInverseImageExact C J φ)

/-- `derivedTransitionCompIso` is the exact-functor composition comparison. -/
theorem derivedTransitionCompIso_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedTransitionCompIso C J φ =
      CategoryTheory.ExactFunctor.MapDerivedCategory.compFunctorIso
        (derivedComponentExact C J m) (abelianInverseImageExact C J φ) :=
  sorry

/-- The comparison out of `D(component m ⋙ f_φ⁻¹)` induced by `abelianTransitionNatTrans`. -/
def derivedTransitionComposite {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    ((component C J AddCommGrpCat.{w} m ⋙
        (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
          (J m).toGrothendieck (J n).toGrothendieck).mapDerivedCategory).obj K ⟶
    (derivedComponent C J n).obj K :=
  (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      ((component C J AddCommGrpCat.{w} m ⋙
          (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
            (J m).toGrothendieck (J n).toGrothendieck).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      ((component C J AddCommGrpCat.{w} n).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (component C J AddCommGrpCat.{w} m ⋙
          (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
            (J m).toGrothendieck (J n).toGrothendieck).mapDerivedCategory
      (component C J AddCommGrpCat.{w} n).mapDerivedCategory
      (whiskerRight (NatTrans.mapHomologicalComplex (abelianTransitionNatTrans C J φ)
          (ComplexShape.up ℤ))
        DerivedCategory.Q)).app K

/-- The comparison `f_φ⁻¹ K_m ⟶ K_n` of objects of `D(C_total)`. -/
def derivedTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (abelianInverseImage C J φ).mapDerivedCategory.obj ((derivedComponent C J m).obj K) ⟶
      (derivedComponent C J n).obj K :=
  (derivedTransitionCompIso C J φ).inv.app K ≫ derivedTransitionComposite C J φ K

/-- `derivedTransition` is the composite comparison conjugated by exactness of `f_φ⁻¹`. -/
theorem derivedTransition_eq {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    derivedTransition C J φ K =
      (derivedTransitionCompIso C J φ).inv.app K ≫ derivedTransitionComposite C J φ K :=
  sorry

end CategoryTheory.SimplicialSites
