module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import stacks_project.Chap85.Lemma_85_11_1_Component
public import stacks_project.Chap85.Situation_85_3_3_MorphismDiagram

/-!
# Ringed simplex operators on a simplicial site

The morphism of ringed topoi `f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)` attached to a simplex
operator, together with the derived-pullback identifications
`Lf_{φ ∘ ψ}^* = Lf_φ^* ∘ Lf_ψ^*` and the identity comparison on each stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open Functor
open ComplexShape

noncomputable section

universe u v w uA vA

namespace CategoryTheory.SimplicialSites

-- The canonical additivity theorem supplies inference for the homotopy functors
-- used below; this adds no hypothesis or new pullback construction.
attribute [instance] RingedSite.ToposHom.modulePullback_additive

/-- Reconstruct a module morphism from an underlying type-valued sheaf map. -/
def moduleHomOfUnderlying {Y : RingedSite.{u, v, w}}
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    {M N : SheafOfModules.{w} Y.structureSheaf}
    (α : (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj M ⟶
      (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj N) :
    M ⟶ N :=
  Sheaf.InternalModule.homOfUnderlying Y.structureSheaf α sorry sorry

/-- Lift an underlying-sheaf isomorphism of module functors to a module-functor isomorphism. -/
def moduleIsoOfUnderlying {X Y : RingedSite.{u, v, w}}
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    {F G : SheafOfModules.{w} X.structureSheaf ⥤ SheafOfModules.{w} Y.structureSheaf}
    (e : F ⋙ Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf ≅
      G ⋙ Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf) :
    F ≅ G :=
  NatIso.ofComponents
    (fun M ↦
      { hom := moduleHomOfUnderlying (e.hom.app M)
        inv := moduleHomOfUnderlying (e.inv.app M)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Canonical derived-category structure on modules over a ringed site. -/
instance instHasDerivedCategory_moduleCat (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, w}] :
    HasDerivedCategory (SheafOfModules.{w} X.structureSheaf) :=
  Hom.moduleCat_hasDerivedCategory.{w, u, v, w} X

/-- Identity on cochain complexes induces the identity on the homotopy category. -/
def mapHomotopyCategoryIdIso {A : Type uA} [Category.{vA} A] [Preadditive A] :
    (𝟭 A).mapHomotopyCategory (up ℤ) ≅ 𝟭 (HomotopyCategory A (up ℤ)) :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (up ℤ))
      (HomotopyCategory.quotient A (up ℤ)))

section ToposHomComparisons

variable {X Y Z : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (f : ToposHom X Y) (g : ToposHom Y Z) (h : ToposHom X Z)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} h.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (f.comp g).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (ToposHom.id X).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived f]
variable [ToposHom.HasModulePullbackDerived g]
variable [ToposHom.HasModulePullbackDerived h]

/-- Underlying type-valued sheaves identify the composite of module pushforwards along `f` and `g`
with module pushforward along `f.comp g`. -/
def modulePushforwardCompUnderlyingIso :
    (f.modulePushforward ⋙ g.modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying Z.structureSheaf ≅
      (f.comp g).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying Z.structureSheaf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft f.modulePushforward (ToposHom.ModulePushforward.forgetIso g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ToposHom.ModulePushforward.forgetIso f) g.toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    (ToposHom.ModulePushforward.forgetIso (f.comp g)).symm

/-- Module pushforwards along `f` and `g` compose as `(f.comp g)_*`. -/
def modulePushforwardCompIso :
    f.modulePushforward ⋙ g.modulePushforward ≅ (f.comp g).modulePushforward :=
  moduleIsoOfUnderlying (modulePushforwardCompUnderlyingIso f g)

/-- Underived module pullbacks along `f` and `g` compose as `(f.comp g)^*`. -/
def modulePullbackCompIso :
    (f.comp g).modulePullback ≅ g.modulePullback ⋙ f.modulePullback :=
  (Adjunction.leftAdjointCompIso g.moduleAdjunction f.moduleAdjunction
      (f.comp g).moduleAdjunction (modulePushforwardCompIso f g)).symm

/-- Underlying type-valued sheaves identify module pushforward along `ToposHom.id` with the
identity. -/
def modulePushforwardIdUnderlyingIso :
    (ToposHom.id X).modulePushforward ⋙
      Sheaf.InternalModule.ToInternal.underlying X.structureSheaf ≅
      𝟭 (SheafOfModules.{w} X.structureSheaf) ⋙
        Sheaf.InternalModule.ToInternal.underlying X.structureSheaf :=
  ToposHom.ModulePushforward.forgetIso (ToposHom.id X) ≪≫
    (Functor.rightUnitor _).symm

/-- Module pushforward along `ToposHom.id` is the identity. -/
def modulePushforwardIdIso :
    (ToposHom.id X).modulePushforward ≅ 𝟭 (SheafOfModules.{w} X.structureSheaf) :=
  moduleIsoOfUnderlying (modulePushforwardIdUnderlyingIso)

/-- Underived module pullback along `ToposHom.id` is the identity. -/
def modulePullbackIdIso :
    (ToposHom.id X).modulePullback ≅ 𝟭 (SheafOfModules.{w} X.structureSheaf) :=
  Adjunction.leftAdjointIdIso (ToposHom.id X).moduleAdjunction modulePushforwardIdIso

variable (hcomp : h.modulePullback ≅ g.modulePullback ⋙ f.modulePullback)

/-- Homotopy-to-derived pullback along `h` identifies with the iterated homotopy-level model of
`g` then `f`. -/
def derivedPullbackCompToDerivedIso :
    ToposHom.modulePullbackToDerived h ≅
      g.modulePullback.mapHomotopyCategory (up ℤ) ⋙ ToposHom.modulePullbackToDerived f :=
  Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso hcomp.symm (up ℤ)).symm
      (Hom.moduleLocalization X) ≪≫
    Functor.associator _ _ _

/-- Iterated counit from `Lf_f^* ∘ Lf_g^*` to the homotopy-level model of `g` then `f`. -/
def derivedPullbackCompCounit :
    Hom.moduleLocalization Z ⋙ (g.modulePullbackDerived ⋙ f.modulePullbackDerived) ⟶
      g.modulePullback.mapHomotopyCategory (up ℤ) ⋙ ToposHom.modulePullbackToDerived f :=
  (Functor.associator (Hom.moduleLocalization Z) g.modulePullbackDerived
      f.modulePullbackDerived).inv ≫
    Functor.whiskerRight
      ((ToposHom.modulePullbackToDerived g).totalLeftDerivedCounit
        (Hom.moduleLocalization Z) (Hom.ModuleQis Z))
      f.modulePullbackDerived ≫
    (Functor.associator (g.modulePullback.mapHomotopyCategory (up ℤ))
      (Hom.moduleLocalization Y) f.modulePullbackDerived).hom ≫
    Functor.whiskerLeft (g.modulePullback.mapHomotopyCategory (up ℤ))
      ((ToposHom.modulePullbackToDerived f).totalLeftDerivedCounit
        (Hom.moduleLocalization Y) (Hom.ModuleQis Y))

/-- Canonical comparison `Lf_f^* ∘ Lf_g^* ⟶ Lf_h^*` of derived module pullbacks, for an underived
identification `h^* ≅ g^* ⋙ f^*`. -/
def derivedPullbackCompComparisonOf :
    g.modulePullbackDerived ⋙ f.modulePullbackDerived ⟶ h.modulePullbackDerived :=
  h.modulePullbackDerived.leftDerivedLift
    ((ToposHom.modulePullbackToDerived h).totalLeftDerivedCounit
      (Hom.moduleLocalization Z) (Hom.ModuleQis Z))
    (Hom.ModuleQis Z) (g.modulePullbackDerived ⋙ f.modulePullbackDerived)
    (derivedPullbackCompCounit f g ≫ (derivedPullbackCompToDerivedIso f g h hcomp).inv)

/-- Component of `derivedPullbackCompComparisonOf` on an object of `D(O_Z)`. -/
theorem derivedPullbackCompComparisonOf_app (K : Hom.ModuleDerived.{w} Z) :
    (derivedPullbackCompComparisonOf f g h hcomp).app K =
      (h.modulePullbackDerived.leftDerivedLift
        ((ToposHom.modulePullbackToDerived h).totalLeftDerivedCounit
          (Hom.moduleLocalization Z) (Hom.ModuleQis Z))
        (Hom.ModuleQis Z) (g.modulePullbackDerived ⋙ f.modulePullbackDerived)
        (derivedPullbackCompCounit f g ≫ (derivedPullbackCompToDerivedIso f g h hcomp).inv)).app K :=
  sorry

/-- The composition comparison of derived module pullbacks is an isomorphism. -/
instance derivedPullbackCompComparisonOf_isIso :
    IsIso (derivedPullbackCompComparisonOf f g h hcomp) :=
  sorry

end ToposHomComparisons

section ToposHomIdComparisons

variable {X : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (h : ToposHom X X)
variable [(SheafOfModules.restrictScalars.{w} h.structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived h]
variable (hid : h.modulePullback ≅ 𝟭 (SheafOfModules.{w} X.structureSheaf))

/-- Homotopy-to-derived pullback along `h` is localization `Qh` after an underived identity
identification. -/
def derivedPullbackIdSourceIsoOf :
    ToposHom.modulePullbackToDerived h ≅ Hom.moduleLocalization X :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso hid ≪≫
        mapHomotopyCategoryIdIso)
      (Hom.moduleLocalization X) ≪≫
    Functor.leftUnitor _

/-- Counit presenting the identity of `D(O_X)` as a left-derived model of `Lf_h^*`. -/
def derivedPullbackIdCounitOf :
    Hom.moduleLocalization X ⋙ 𝟭 (Hom.ModuleDerived.{w} X) ⟶
      ToposHom.modulePullbackToDerived h :=
  (Functor.rightUnitor (Hom.moduleLocalization X)).hom ≫
    (derivedPullbackIdSourceIsoOf h hid).inv

/-- Canonical comparison `id ⟶ Lf_h^*` of derived module pullbacks. -/
def derivedPullbackIdComparisonOf :
    𝟭 (Hom.ModuleDerived.{w} X) ⟶ h.modulePullbackDerived :=
  h.modulePullbackDerived.leftDerivedLift
    ((ToposHom.modulePullbackToDerived h).totalLeftDerivedCounit
      (Hom.moduleLocalization X) (Hom.ModuleQis X))
    (Hom.ModuleQis X) (𝟭 (Hom.ModuleDerived.{w} X)) (derivedPullbackIdCounitOf h hid)

/-- Component of `derivedPullbackIdComparisonOf` on an object of `D(O_X)`. -/
theorem derivedPullbackIdComparisonOf_app (K : Hom.ModuleDerived.{w} X) :
    (derivedPullbackIdComparisonOf h hid).app K =
      (h.modulePullbackDerived.leftDerivedLift
        ((ToposHom.modulePullbackToDerived h).totalLeftDerivedCounit
          (Hom.moduleLocalization X) (Hom.ModuleQis X))
        (Hom.ModuleQis X) (𝟭 (Hom.ModuleDerived.{w} X))
        (derivedPullbackIdCounitOf h hid)).app K :=
  sorry

/-- The identity comparison of derived module pullbacks is an isomorphism. -/
instance derivedPullbackIdComparisonOf_isIso :
    IsIso (derivedPullbackIdComparisonOf h hid) :=
  sorry

end ToposHomIdComparisons

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]

/-- The natural transformation `(C.map φ) ⋙ ofStage n ⟶ ofStage m` whose component at `U`
is the total-category morphism `(φ, 𝟙 (u_φ U))`. -/
def ofStageNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.map φ).toFunctor ⋙ ofStage C n ⟶ ofStage C m where
  app U :=
    homMk φ (𝟙 ((C.map φ).toFunctor.obj U))
  naturality := sorry

/-- The composite `u_φ ⋙ ofStage n` is continuous for the stage and total topologies. -/
instance ofStage_comp_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    ((C.map φ).toFunctor ⋙ ofStage C n).IsContinuous
      (J m).toGrothendieck (topology C J) :=
  Functor.isContinuous_comp (C.map φ).toFunctor (ofStage C n)
    (J m).toGrothendieck (J n).toGrothendieck (topology C J)

/-- Structure maps of a morphism diagram have left-exact sheaf pullback. -/
instance toFunctor_sheafPullback_preservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits
      ((C.map φ).toFunctor.sheafPullback (Type w)
        (J m).toGrothendieck (J n).toGrothendieck) :=
  sorry

/-- Direct-image form of `O(φ)`: restriction of `O` along `ofStageNatTrans` yields
`O_m ⟶ (u_φ)_* O_n`. -/
def ringedToposMapDirectStructure {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentRingedSite C J O m).structureSheaf ⟶
      ((C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck).obj
        (componentRingedSite C J O n).structureSheaf :=
  (sheafPushforwardContinuousNatTrans (ofStageNatTrans C φ) RingCat.{w}
      (J m).toGrothendieck (topology C J)).app O ≫
    (sheafPushforwardContinuousComp (C.map φ).toFunctor (ofStage C n) RingCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck (topology C J)).inv.app O

/-- Coefficient-forgetful comparison for continuous ring-valued pushforward along `u_φ`. -/
def ringedToposMapForgetIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
          (J m).toGrothendieck (J n).toGrothendieck ⋙
        sheafCompose (J m).toGrothendieck (forget RingCat.{w}) ≅
      sheafCompose (J n).toGrothendieck (forget RingCat.{w}) ⋙
        (C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
          (J m).toGrothendieck (J n).toGrothendieck :=
  NatIso.ofComponents
    (fun P ↦
      (fullyFaithfulSheafToPresheaf (J m).toGrothendieck (Type w)).preimageIso
        (Functor.associator ((C.map φ).toFunctor.op) P.obj (forget RingCat.{w})))
    sorry

/-- Ring-compatibility of the direct-image presentation of `O(φ)`. -/
theorem ringedToposMap_isRingCompatible {m n : SimplexCategory} (φ : m ⟶ n) :
    @ToposHom.Direct.IsRingCompatible
      (componentRingedSite C J O n) (componentRingedSite C J O m) _ _
      ((C.map φ).toFunctor.morphismOfTopoiInOfContinuous
        (J m).toGrothendieck (J n).toGrothendieck)
      ((C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck)
      (ringedToposMapForgetIso C J φ) (ringedToposMapDirectStructure C J O φ) :=
  sorry

/-- The morphism of ringed topoi `f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)` with underlying
topos morphism `((C.map φ).toFunctor.morphismOfTopoiInOfContinuous (J m).toGrothendieck (J n).toGrothendieck)` and structure map `O(φ) : f_φ⁻¹ O_m ⟶ O_n`. -/
def ringedToposMap {m n : SimplexCategory} (φ : m ⟶ n) :
    ToposHom (componentRingedSite C J O n) (componentRingedSite C J O m) :=
  @ToposHom.ofDirectImage (componentRingedSite C J O n) (componentRingedSite C J O m) _ _
    ((C.map φ).toFunctor.morphismOfTopoiInOfContinuous
      (J m).toGrothendieck (J n).toGrothendieck)
    ((C.map φ).toFunctor.sheafPushforwardContinuous RingCat.{w}
      (J m).toGrothendieck (J n).toGrothendieck)
    (ringedToposMapForgetIso C J φ) (ringedToposMapDirectStructure C J O φ)
    (ringedToposMap_isRingCompatible C J O φ)

/-- The underlying topos morphism of `ringedToposMap C J O φ` is `((C.map φ).toFunctor.morphismOfTopoiInOfContinuous (J m).toGrothendieck (J n).toGrothendieck)`. -/
theorem ringedToposMap_toTopos {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).toTopos = ((C.map φ).toFunctor.morphismOfTopoiInOfContinuous (J m).toGrothendieck (J n).toGrothendieck) :=
  sorry

/-- Direct images of `ringedToposMap` compose as the ringed-topos composite, on underlying
topos morphisms. -/
theorem ringedToposMap_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).comp (ringedToposMap C J O ψ)).toTopos =
      MorphismOfTopoiIn.comp
        ((C.map ψ).toFunctor.morphismOfTopoiInOfContinuous
          (J l).toGrothendieck (J m).toGrothendieck)
        ((C.map φ).toFunctor.morphismOfTopoiInOfContinuous
          (J m).toGrothendieck (J n).toGrothendieck) :=
  sorry

variable [UnivLE.{max u v, w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Underlying type-valued sheaves identify the composite of module pushforwards along
`ringedToposMap ψ` and `ringedToposMap φ` with module pushforward along `ringedToposMap (ψ ≫ φ)`. -/
def ringedModulePushforwardCompUnderlyingIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).modulePushforward ⋙
        (ringedToposMap C J O ψ).modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying
        (componentRingedSite C J O l).structureSheaf ≅
      (ringedToposMap C J O (ψ ≫ φ)).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying
          (componentRingedSite C J O l).structureSheaf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ringedToposMap C J O φ).modulePushforward
      (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O ψ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ))
      (ringedToposMap C J O ψ).toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying
        (componentRingedSite C J O n).structureSheaf)
      (sheafPushforwardContinuousComp' (map_comp_toFunctor C ψ φ) (Type w)
        (J l).toGrothendieck (J m).toGrothendieck (J n).toGrothendieck) ≪≫
    (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O (ψ ≫ φ))).symm

/-- Module pushforwards along `ringedToposMap` compose as `f_{ψ ≫ φ,*}`. -/
def ringedModulePushforwardCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePushforward ⋙
      (ringedToposMap C J O ψ).modulePushforward ≅
      (ringedToposMap C J O (ψ ≫ φ)).modulePushforward :=
  moduleIsoOfUnderlying (ringedModulePushforwardCompUnderlyingIso C J O ψ φ)

/-- Underived module pullbacks along `ringedToposMap` compose as `f_{ψ ≫ φ}^*`. -/
def ringedModulePullbackCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (ringedToposMap C J O (ψ ≫ φ)).modulePullback ≅
      (ringedToposMap C J O ψ).modulePullback ⋙
        (ringedToposMap C J O φ).modulePullback :=
  (Adjunction.leftAdjointCompIso
      (ringedToposMap C J O ψ).moduleAdjunction
      (ringedToposMap C J O φ).moduleAdjunction
      (ringedToposMap C J O (ψ ≫ φ)).moduleAdjunction
      (ringedModulePushforwardCompIso C J O ψ φ)).symm

/-- The functor `(C.map (𝟙 n)).toFunctor` is the identity on the stage category. -/
def map_id_toFunctor (n : SimplexCategory) :
    (C.map (𝟙 n)).toFunctor ≅ 𝟭 (C.obj n) :=
  Cat.Hom.toNatIso (eqToIso (C.map_id n))

/-- Underlying type-valued sheaves identify module pushforward along `ringedToposMap (𝟙 n)`
with the identity. -/
def ringedModulePushforwardIdUnderlyingIso (n : SimplexCategory) :
    (ringedToposMap C J O (𝟙 n)).modulePushforward ⋙
      Sheaf.InternalModule.ToInternal.underlying
        (componentRingedSite C J O n).structureSheaf ≅
      𝟭 (SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) ⋙
        Sheaf.InternalModule.ToInternal.underlying
          (componentRingedSite C J O n).structureSheaf :=
  ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O (𝟙 n)) ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying
        (componentRingedSite C J O n).structureSheaf)
      (sheafPushforwardContinuousId' (map_id_toFunctor C n) (Type w)
        (J n).toGrothendieck) ≪≫
    (Functor.rightUnitor _).symm

/-- Module pushforward along `ringedToposMap (𝟙 n)` is the identity. -/
def ringedModulePushforwardIdIso (n : SimplexCategory) :
    (ringedToposMap C J O (𝟙 n)).modulePushforward ≅
      𝟭 (SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) :=
  moduleIsoOfUnderlying (ringedModulePushforwardIdUnderlyingIso C J O n)

/-- Underived module pullback along `ringedToposMap (𝟙 n)` is the identity. -/
def ringedModulePullbackIdIso (n : SimplexCategory) :
    (ringedToposMap C J O (𝟙 n)).modulePullback ≅
      𝟭 (SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) :=
  Adjunction.leftAdjointIdIso
    (ringedToposMap C J O (𝟙 n)).moduleAdjunction
    (ringedModulePushforwardIdIso C J O n)

/-- Module pullback along `ringedToposMap φ` is additive. -/
instance ringedToposMap_modulePullback_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePullback.Additive :=
  ToposHom.modulePullback_additive (ringedToposMap C J O φ)

/-- Canonical comparison `Lf_φ^* ∘ Lf_ψ^* ⟶ Lf_{ψ ≫ φ}^*` of derived module pullbacks. -/
def derivedPullbackCompComparison {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (ringedToposMap C J O ψ).modulePullbackDerived ⋙
      (ringedToposMap C J O φ).modulePullbackDerived ⟶
      (ringedToposMap C J O (ψ ≫ φ)).modulePullbackDerived :=
  derivedPullbackCompComparisonOf
    (ringedToposMap C J O φ) (ringedToposMap C J O ψ) (ringedToposMap C J O (ψ ≫ φ))
    (ringedModulePullbackCompIso C J O ψ φ)

/-- Component of `derivedPullbackCompComparison` on an object of `D(O_l)`. -/
theorem derivedPullbackCompComparison_app {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : Hom.ModuleDerived.{w} (componentRingedSite C J O l)) :
    (derivedPullbackCompComparison C J O ψ φ).app K =
      (derivedPullbackCompComparisonOf
        (ringedToposMap C J O φ) (ringedToposMap C J O ψ)
        (ringedToposMap C J O (ψ ≫ φ)) (ringedModulePullbackCompIso C J O ψ φ)).app K :=
  sorry

/-- The composition comparison of derived module pullbacks is an isomorphism. -/
instance derivedPullbackCompComparison_isIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    IsIso (derivedPullbackCompComparison C J O ψ φ) :=
  sorry

/-- Canonical comparison `id ⟶ Lf_id^*` of derived module pullbacks on a stage. -/
def derivedPullbackIdComparison (n : SimplexCategory) :
    𝟭 (Hom.ModuleDerived.{w} (componentRingedSite C J O n)) ⟶
      (ringedToposMap C J O (𝟙 n)).modulePullbackDerived :=
  derivedPullbackIdComparisonOf (ringedToposMap C J O (𝟙 n))
    (ringedModulePullbackIdIso C J O n)

/-- Component of `derivedPullbackIdComparison` on an object of `D(O_n)`. -/
theorem derivedPullbackIdComparison_app (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (componentRingedSite C J O n)) :
    (derivedPullbackIdComparison C J O n).app K =
      (derivedPullbackIdComparisonOf (ringedToposMap C J O (𝟙 n))
        (ringedModulePullbackIdIso C J O n)).app K :=
  sorry

/-- The identity comparison of derived module pullbacks is an isomorphism. -/
instance derivedPullbackIdComparison_isIso (n : SimplexCategory) :
    IsIso (derivedPullbackIdComparison C J O n) :=
  sorry

end CategoryTheory.SimplicialSites
