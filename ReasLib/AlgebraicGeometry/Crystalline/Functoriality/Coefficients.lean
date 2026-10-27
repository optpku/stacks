/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism
public import ReasLib.AlgebraicGeometry.Crystalline.ZariskiComparison.SmallBig
public import ReasLib.AlgebraicGeometry.Crystalline.Pushforward.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.SiteSized
public import ReasLib.CategoryTheory.Sites.Topos.Abelian
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import ReasLib.CategoryTheory.Functor.Derived.Exact

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
variable {X' : Scheme.{u}} (f : X' ⟶ B.source) (x'₀ : X' ⟶ B.ideal.subscheme)
variable (h_over : f ≫ B.sourceToClosed = x'₀)
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

include h_over in
/-- A morphism over the closed fibre gives the source square for the identity
divided-power morphism on the fixed crystalline base. -/
theorem sameBase_closedSquare :
    f ≫ B.sourceToClosed = x'₀ ≫
      (DividedPowerScheme.Hom.id B.dividedPowerScheme).zeroFiberMap := sorry

/-- The morphism of small crystalline ringed topoi induced by a scheme map over
a fixed prime-local divided-power base. -/
def sameBaseRingedMorphism :
    RingedSite.ToposHom (B.withSource X' x'₀ h_p').ringedSite B.ringedSite :=
  Ringed.morphism (B.withSource X' x'₀ h_p') B
    (DividedPowerScheme.Hom.id B.dividedPowerScheme) (Category.id_comp _) f
    (sameBase_closedSquare B f x'₀ h_over)

/-- Pullback of crystalline module sheaves includes geometric inverse image and
extension of scalars to the crystalline structure sheaf of the source. -/
def crystalPullback := (sameBaseRingedMorphism B f x'₀ h_over h_p').modulePullback

/-- Crystalline module pullback is the module inverse image of the canonical
fixed-base ringed-topos morphism. -/
theorem crystalPullback_spec :
    crystalPullback B f x'₀ h_over h_p' =
      (sameBaseRingedMorphism B f x'₀ h_over h_p').modulePullback := sorry

/-- The underlying section function comparing module direct image with abelian
direct image is the composite of the canonical forgetful isomorphisms. -/
def modulePushforwardAbelianComparisonAppFun
    (M : SheafOfModules (B.withSource X' x'₀ h_p').liftedStructureSheaf)
    (U : B.ringedSite.carrierᵒᵖ) :
    (((SheafOfModules.toSheaf _).obj
      ((sameBaseRingedMorphism B f x'₀ h_over h_p').modulePushforward.obj M)).obj.obj U) →
    (((sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage.obj
      ((SheafOfModules.toSheaf _).obj M)).obj.obj U) :=
  fun x ↦
    (((sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImageForgetIso).inv.app
      ((SheafOfModules.toSheaf _).obj M)).hom.app U
      (((RingedSite.ToposHom.ModulePushforward.forgetIso
        (sameBaseRingedMorphism B f x'₀ h_over h_p')).hom.app M).hom.app U x)

/-- The module-to-abelian direct-image section comparison preserves addition. -/
theorem modulePushforwardAbelianComparison_map_add
    (M : SheafOfModules (B.withSource X' x'₀ h_p').liftedStructureSheaf)
    (U : B.ringedSite.carrierᵒᵖ) (x y :
      ((SheafOfModules.toSheaf _).obj
        ((sameBaseRingedMorphism B f x'₀ h_over h_p').modulePushforward.obj M)).obj.obj U) :
    modulePushforwardAbelianComparisonAppFun B f x'₀ h_over h_p' M U (x + y) =
      modulePushforwardAbelianComparisonAppFun B f x'₀ h_over h_p' M U x +
        modulePushforwardAbelianComparisonAppFun B f x'₀ h_over h_p' M U y := sorry

/-- The additive component of the underlying module direct-image comparison. -/
def modulePushforwardAbelianComparisonApp (M : SheafOfModules (B.withSource X' x'₀ h_p').liftedStructureSheaf)
    (U : B.ringedSite.carrierᵒᵖ) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (modulePushforwardAbelianComparisonAppFun B f x'₀ h_over h_p' M U)
    (modulePushforwardAbelianComparison_map_add B f x'₀ h_over h_p' M U))

/-- The additive section comparisons commute with restriction maps and with
morphisms of module sheaves. -/
theorem modulePushforwardAbelianComparison_naturality :
    (∀ (M : SheafOfModules (B.withSource X' x'₀ h_p').liftedStructureSheaf)
        {U V : B.ringedSite.carrierᵒᵖ} (a : U ⟶ V),
      ((((sameBaseRingedMorphism B f x'₀ h_over h_p').modulePushforward ⋙ SheafOfModules.toSheaf B.liftedStructureSheaf).obj M).obj.map a) ≫
          modulePushforwardAbelianComparisonApp B f x'₀ h_over h_p' M V =
        modulePushforwardAbelianComparisonApp B f x'₀ h_over h_p' M U ≫
          (((SheafOfModules.toSheaf (B.withSource X' x'₀ h_p').liftedStructureSheaf ⋙
      (sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage).obj M).obj.map a)) ∧
    (∀ {M N : SheafOfModules (B.withSource X' x'₀ h_p').liftedStructureSheaf} (a : M ⟶ N) (U : B.ringedSite.carrierᵒᵖ),
      (((sameBaseRingedMorphism B f x'₀ h_over h_p').modulePushforward ⋙ SheafOfModules.toSheaf B.liftedStructureSheaf).map a).hom.app U ≫
          modulePushforwardAbelianComparisonApp B f x'₀ h_over h_p' N U =
        modulePushforwardAbelianComparisonApp B f x'₀ h_over h_p' M U ≫
          ((SheafOfModules.toSheaf (B.withSource X' x'₀ h_p').liftedStructureSheaf ⋙
      (sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage).map a).hom.app U) := sorry

/-- Forgetting module structure commutes canonically with direct image of
crystalline coefficients as abelian sheaves. -/
def modulePushforwardAbelianComparison :
    (sameBaseRingedMorphism B f x'₀ h_over h_p').modulePushforward ⋙ SheafOfModules.toSheaf B.liftedStructureSheaf ⟶
    SheafOfModules.toSheaf (B.withSource X' x'₀ h_p').liftedStructureSheaf ⋙
      (sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage where
  app M := ObjectProperty.homMk
    { app := modulePushforwardAbelianComparisonApp B f x'₀ h_over h_p' M
      naturality := fun {_ _} a ↦
        (modulePushforwardAbelianComparison_naturality B f x'₀ h_over h_p').1 M a }
  naturality {M N} a := ObjectProperty.hom_ext _
    (NatTrans.ext (funext ((modulePushforwardAbelianComparison_naturality B f x'₀ h_over h_p').2 a)))

/-- The module-to-abelian direct-image comparison is invertible. -/
@[instance] theorem modulePushforwardAbelianComparison_isIso :
    IsIso (modulePushforwardAbelianComparison B f x'₀ h_over h_p') := sorry

/-- The section function comparing crystalline direct image followed by Zariski
restriction with Zariski direct image after crystalline restriction. -/
def crystallinePushforwardSquareComparisonAppFun
    (M : Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1})
    (U : B.source.smallZariskiSiteᵒᵖ) :
    ((smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
      B.sourceToClosed B.prime_nilpotent).obj
        ((sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage.obj M)).obj.obj U →
    ((zariskiAbelianPushforward.{u, u + 1} f).obj
      ((smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
        x'₀ h_p').obj M)).obj.obj U :=
  let geometric :
        (sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.pushforward ⋙
          (forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
            B.source B.sourceToClosed B.prime_nilpotent).sheafPushforwardCocontinuous
            (Type (u + 1)) B.ringedSite.siteTopology B.source.smallZariskiTopology ⟶
        (forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
            X' x'₀ h_p').sheafPushforwardCocontinuous (Type (u + 1))
            (B.withSource X' x'₀ h_p').ringedSite.siteTopology X'.smallZariskiTopology ⋙
          (smallZariskiPullback f).sheafPushforwardContinuous (Type (u + 1))
            B.source.smallZariskiTopology X'.smallZariskiTopology
      :=
    let C := B.withSource X' x'₀ h_p'
    let d := DividedPowerScheme.Hom.id B.dividedPowerScheme
    let hf := sameBase_closedSquare B f x'₀ h_over
    let c := Ringed.baseChangeFunctor C B d f hf
    let b := crystallineForgetful B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent
    let b' := crystallineForgetful C.scheme C.ideal C.dividedPowers C.compatible
      C.toSpec C.source C.sourceToClosed C.prime_nilpotent
    let a := forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent
    let a' := forgetfulFunctor p C.scheme C.ideal C.dividedPowers C.compatible
      C.toSpec C.source C.sourceToClosed C.prime_nilpotent
    let i' := smallCrystallineInclusion C.scheme C.ideal C.dividedPowers C.compatible
      C.source C.sourceToClosed
    let j := Zariski.SmallToBig.relocalizationFunctor (𝟙 B.source)
    let j' := Zariski.SmallToBig.relocalizationFunctor (𝟙 C.source)
    let cPush := (Ringed.bigMorphism C B d f hf).toTopos.pushforward
    let iPush := (Ringed.smallToBig C).toTopos.pushforward
    let jPush := j.sheafPushforwardContinuous (Type (u + 1))
      B.source.smallZariskiTopology B.source.bigZariskiTopology
    let b'Push := C.zariskiToposMorphism.pushforward
    let zPush := (smallZariskiPullback f).sheafPushforwardContinuous (Type (u + 1))
      B.source.smallZariskiTopology C.source.smallZariskiTopology
    let a'Push := a'.sheafPushforwardCocontinuous (Type (u + 1))
      C.ringedSite.siteTopology C.source.smallZariskiTopology
    let targetComparison := smallBigZariskiComparisonIso.{u, u + 1}
      B.ideal B.dividedPowers B.compatible B.toSpec B.sourceToClosed B.prime_nilpotent
      (h_quasiCoherent := B.quasiCoherent)
    let sourceComparison := smallBigZariskiComparisonIso.{u, u + 1}
      C.ideal C.dividedPowers C.compatible C.toSpec C.sourceToClosed C.prime_nilpotent
      (h_quasiCoherent := C.quasiCoherent)
    let bigLeft := @Functor.sheafPushforwardCocontinuousComp _ _ _ _ _ _
      C.bigRingedSite.siteTopology B.bigRingedSite.siteTopology B.source.bigZariskiTopology c b
      (Ringed.baseChangeFunctor_isCocontinuous C B d f hf)
      (crystallineForgetful_isCocontinuous B.scheme B.ideal
        (h_quasiCoherent := B.quasiCoherent) B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent)
      (Type (u + 1)) inferInstance inferInstance inferInstance inferInstance
    let bigRight := @Functor.sheafPushforwardCocontinuousComp _ _ _ _ _ _
      C.bigRingedSite.siteTopology C.source.bigZariskiTopology B.source.bigZariskiTopology
      b' (Over.map f)
      (crystallineForgetful_isCocontinuous C.scheme C.ideal
        (h_quasiCoherent := C.quasiCoherent) C.dividedPowers C.compatible C.toSpec
        C.source C.sourceToClosed C.prime_nilpotent)
      inferInstance (Type (u + 1)) inferInstance inferInstance inferInstance inferInstance
    let bigComparison : cPush ⋙ B.zariskiToposMorphism.pushforward ≅
        b'Push ⋙ Zariski.Big.directImage f := bigLeft ≪≫ bigRight.symm
    let forgetSource := MorphismProperty.Over.forget @IsOpenImmersion ⊤ C.source
    let forgetTarget := MorphismProperty.Over.forget @IsOpenImmersion ⊤ B.source
    let jSourceIso : j' ≅ forgetSource :=
      Functor.isoWhiskerLeft forgetSource (Over.mapId C.source) ≪≫
        Functor.rightUnitor forgetSource
    let jTargetIso : j ≅ forgetTarget :=
      Functor.isoWhiskerLeft forgetTarget (Over.mapId B.source) ≪≫
        Functor.rightUnitor forgetTarget
    let zSquare : smallZariskiPullback f ⋙ j' ≅ j ⋙ Over.pullback f :=
      Functor.isoWhiskerLeft (smallZariskiPullback f) jSourceIso ≪≫
        MorphismProperty.Over.pullbackCompForgetIso (P := @IsOpenImmersion) (Q := ⊤) f ≪≫
        Functor.isoWhiskerRight jTargetIso.symm (Over.pullback f)
    let zLeft := @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _
      j (Over.pullback f) (smallZariskiPullback f ⋙ j') zSquare.symm
      (Type (u + 1)) inferInstance B.source.smallZariskiTopology B.source.bigZariskiTopology
      C.source.bigZariskiTopology inferInstance inferInstance
      (Functor.isContinuous_comp (smallZariskiPullback f) j'
        B.source.smallZariskiTopology C.source.smallZariskiTopology C.source.bigZariskiTopology)
    let zComparison : Zariski.Big.directImage f ⋙ jPush ≅
        j'.sheafPushforwardContinuous (Type (u + 1))
          C.source.smallZariskiTopology C.source.bigZariskiTopology ⋙ zPush :=
      Functor.isoWhiskerRight (Zariski.Big.directImageIsoPullbackPresentation f) jPush ≪≫
        zLeft ≪≫ (Functor.sheafPushforwardContinuousComp (smallZariskiPullback f) j'
          (Type (u + 1)) B.source.smallZariskiTopology C.source.smallZariskiTopology
          C.source.bigZariskiTopology).symm
    let counit := i'.sheafAdjunctionCocontinuous (Type (u + 1))
      C.ringedSite.siteTopology C.bigRingedSite.siteTopology
    (Functor.associator iPush (cPush ⋙ (Ringed.bigToSmall B).toTopos.pushforward)
        (a.sheafPushforwardCocontinuous (Type (u + 1)) B.ringedSite.siteTopology
          B.source.smallZariskiTopology)).hom ≫
      Functor.whiskerLeft iPush
        ((Functor.associator cPush (Ringed.bigToSmall B).toTopos.pushforward
            (a.sheafPushforwardCocontinuous (Type (u + 1)) B.ringedSite.siteTopology
              B.source.smallZariskiTopology)).hom ≫
          Functor.whiskerLeft cPush targetComparison.inv ≫
          (Functor.associator cPush B.zariskiToposMorphism.pushforward jPush).inv ≫
          Functor.whiskerRight bigComparison.hom jPush ≫
          (Functor.associator b'Push (Zariski.Big.directImage f) jPush).hom ≫
          Functor.whiskerLeft b'Push zComparison.hom ≫
          (Functor.associator b'Push
            (j'.sheafPushforwardContinuous (Type (u + 1)) C.source.smallZariskiTopology
              C.source.bigZariskiTopology) zPush).inv ≫
          Functor.whiskerRight sourceComparison.hom zPush ≫
          (Functor.associator
            (i'.sheafPushforwardContinuous (Type (u + 1))
              C.ringedSite.siteTopology C.bigRingedSite.siteTopology) a'Push zPush).hom) ≫
      (Functor.associator iPush
        (i'.sheafPushforwardContinuous (Type (u + 1))
          C.ringedSite.siteTopology C.bigRingedSite.siteTopology) (a'Push ⋙ zPush)).inv ≫
      Functor.whiskerRight counit.counit (a'Push ⋙ zPush) ≫
      (Functor.leftUnitor (a'Push ⋙ zPush)).hom
  let C := B.withSource X' x'₀ h_p'
  let a := forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent
  let a' := forgetfulFunctor p C.scheme C.ideal C.dividedPowers C.compatible
    C.toSpec C.source C.sourceToClosed C.prime_nilpotent
  let e := Functor.sheafPushforwardCocontinuous.compSheafComposeIso a
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) B.ringedSite.siteTopology B.source.smallZariskiTopology
  let e' := Functor.sheafPushforwardCocontinuous.compSheafComposeIso a'
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) C.ringedSite.siteTopology C.source.smallZariskiTopology
  let t := (e.hom.app
    ((sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage.obj M)).hom.app U
  let t' := ((a.sheafPushforwardCocontinuous (Type (u + 1))
    B.ringedSite.siteTopology B.source.smallZariskiTopology).map
      ((sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImageForgetIso.hom.app M)).hom.app U
  let t'' := (geometric.app
    ((sheafCompose C.ringedSite.siteTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M)).hom.app U
  let t''' := (((smallZariskiPullback f).sheafPushforwardContinuous (Type (u + 1))
    B.source.smallZariskiTopology X'.smallZariskiTopology).map (e'.inv.app M)).hom.app U
  fun x ↦ t''' (t'' (t' (t x)))

/-- The crystalline–Zariski direct-image section comparison preserves addition. -/
theorem crystallinePushforwardSquareComparison_map_add
    (M : Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1})
    (U : B.source.smallZariskiSiteᵒᵖ) (x y :
      ((smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
        B.sourceToClosed B.prime_nilpotent).obj
          ((sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage.obj M)).obj.obj U) :
    crystallinePushforwardSquareComparisonAppFun B f x'₀ h_over h_p' M U (x + y) =
      crystallinePushforwardSquareComparisonAppFun B f x'₀ h_over h_p' M U x +
        crystallinePushforwardSquareComparisonAppFun B f x'₀ h_over h_p' M U y := sorry

/-- The additive component of the crystalline–Zariski direct-image comparison. -/
def crystallinePushforwardSquareComparisonApp
    (M : Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1})
    (U : B.source.smallZariskiSiteᵒᵖ) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (crystallinePushforwardSquareComparisonAppFun B f x'₀ h_over h_p' M U)
    (crystallinePushforwardSquareComparison_map_add B f x'₀ h_over h_p' M U))

/-- The crystalline–Zariski additive comparisons commute with restriction and
with morphisms of coefficient sheaves. -/
theorem crystallinePushforwardSquareComparison_naturality :
    (∀ (M : Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1})
        {U V : B.source.smallZariskiSiteᵒᵖ} (a : U ⟶ V),
      (((sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage ⋙
        smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
          B.sourceToClosed B.prime_nilpotent).obj M).obj.map a ≫
          crystallinePushforwardSquareComparisonApp B f x'₀ h_over h_p' M V =
        crystallinePushforwardSquareComparisonApp B f x'₀ h_over h_p' M U ≫
          ((smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
            x'₀ h_p' ⋙ zariskiAbelianPushforward.{u, u + 1} f).obj M).obj.map a) ∧
    (∀ {M N : Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1}}
        (a : M ⟶ N) (U : B.source.smallZariskiSiteᵒᵖ),
      (((sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage ⋙
        smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
          B.sourceToClosed B.prime_nilpotent).map a).hom.app U ≫
          crystallinePushforwardSquareComparisonApp B f x'₀ h_over h_p' N U =
        crystallinePushforwardSquareComparisonApp B f x'₀ h_over h_p' M U ≫
          ((smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
            x'₀ h_p' ⋙ zariskiAbelianPushforward.{u, u + 1} f).map a).hom.app U) := sorry

/-- Crystalline direct image commutes with Zariski direct image for a morphism
of schemes over a fixed divided-power base. -/
def crystallinePushforwardSquareComparison :
    (sameBaseRingedMorphism B f x'₀ h_over h_p').toTopos.abelianDirectImage ⋙
      smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
        B.sourceToClosed B.prime_nilpotent ⟶
    smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec x'₀ h_p' ⋙
      zariskiAbelianPushforward.{u, u + 1} f where
  app M := ObjectProperty.homMk
    { app := crystallinePushforwardSquareComparisonApp B f x'₀ h_over h_p' M
      naturality := fun {_ _} a ↦
        (crystallinePushforwardSquareComparison_naturality B f x'₀ h_over h_p').1 M a }
  naturality {M N} a := ObjectProperty.hom_ext _
    (NatTrans.ext (funext
      ((crystallinePushforwardSquareComparison_naturality B f x'₀ h_over h_p').2 a)))

/-- The crystalline–Zariski abelian direct-image comparison is invertible. -/
@[instance] theorem crystallinePushforwardSquareComparison_isIso :
    IsIso (crystallinePushforwardSquareComparison B f x'₀ h_over h_p') := sorry


variable [HasDerivedCategory.{u + 1} (Sheaf B.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1}
  (Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1} (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 1} (Sheaf X'.smallZariskiTopology AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian.{u + 1} (Sheaf B.ringedSite.siteTopology AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian.{u + 1}
  (Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1})]

/-- Crystalline direct image sends K-injective resolutions to resolutions acyclic
for the small crystalline-to-Zariski direct image. The iterated unit retains
its universal property after an isomorphic presentation of its source. -/
theorem crystallinePushforwardAcyclic :
  let r := sameBaseRingedMorphism B f x'₀ h_over h_p'
  let P : Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1} ⥤+
      Sheaf B.ringedSite.siteTopology AddCommGrpCat.{u + 1} :=
    (AdditiveFunctor.ofLeftExact _ _).obj
      ⟨r.toTopos.abelianDirectImage,
        ⟨fun _ _ _ ↦ r.toTopos.abelianAdjunction.rightAdjoint_preservesLimits.preservesLimitsOfShape⟩⟩
  let UC := smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible
    B.toSpec B.sourceToClosed B.prime_nilpotent
  ∀ (V : CochainComplex
      (Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1}) ℤ ⥤
        DerivedCategory (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u + 1}))
      (e : V ≅ P.obj.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (UC.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)),
    (Functor.RightDerived.KInjective.functor P.obj ⋙
      Functor.RightDerived.KInjective.functor UC).IsRightDerivedFunctor
        (e.hom ≫ Functor.RightDerived.Composition.iteratedUnit
          (Functor.RightDerived.KInjective.unit P.obj)
          (Functor.RightDerived.KInjective.unit UC))
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) := sorry

/-- Zariski direct image along a homeomorphism has no higher right-derived
contribution on a sheaf concentrated in degree zero. -/
theorem zariskiPushforwardAcyclic (hf : IsHomeomorph f)
    (M : Sheaf X'.smallZariskiTopology AddCommGrpCat.{u + 1}) :
    Functor.RightAcyclic (zariskiAbelianPushforwardExact.{u, u + 1} f hf).obj M := sorry

set_option maxHeartbeats 800000 in
/-- The canonical derived comparison for crystalline module coefficients is
induced by the module adjunction unit and the crystalline–Zariski square. -/
def crystallineComparison (hf : IsHomeomorph f)
    (F : SheafOfModules.{u + 1} B.liftedStructureSheaf) :
    derivedSmallCrystallinePushforward_obj.{u, u + 1, u + 1, u + 1, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
      B.sourceToClosed B.prime_nilpotent ((SheafOfModules.toSheaf _).obj F) ⟶
    (zariskiAbelianPushforwardExact.{u, u + 1} f hf).mapDerivedCategory.obj
      (derivedSmallCrystallinePushforward_obj.{u, u + 1, u + 1, u + 1, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
        x'₀ h_p' ((SheafOfModules.toSheaf _).obj
          ((crystalPullback B f x'₀ h_over h_p').obj F))) :=
  let r := sameBaseRingedMorphism B f x'₀ h_over h_p'
  let P : Sheaf (B.withSource X' x'₀ h_p').ringedSite.siteTopology AddCommGrpCat.{u + 1} ⥤+
      Sheaf B.ringedSite.siteTopology AddCommGrpCat.{u + 1} :=
    (AdditiveFunctor.ofLeftExact _ _).obj
      ⟨r.toTopos.abelianDirectImage,
        ⟨fun _ _ _ ↦ r.toTopos.abelianAdjunction.rightAdjoint_preservesLimits.preservesLimitsOfShape⟩⟩
  let UC := smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible
    B.toSpec B.sourceToClosed B.prime_nilpotent
  let UD := smallCrystallinePushforward.{u, u + 1} B.ideal B.dividedPowers B.compatible
    B.toSpec x'₀ h_p'
  let Z := zariskiAbelianPushforwardExact.{u, u + 1} f hf
  let e : P.obj ⋙ UC ≅ UD ⋙ Z.obj :=
    @asIso _ _ _ _ (crystallinePushforwardSquareComparison B f x'₀ h_over h_p')
      (crystallinePushforwardSquareComparison_isIso B f x'₀ h_over h_p')
  let eC := Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (UD ⋙ Z.obj)) (ComplexShape.up ℤ)).symm
  let αP := Functor.RightDerived.KInjective.unit P.obj
  let αUC := Functor.RightDerived.KInjective.unit UC
  let αUD := Functor.RightDerived.KInjective.unit UD
  let αZ := Z.obj.mapDerivedCategoryFactors.inv
  let eSource :=
    (Functor.associator (UD.mapHomologicalComplex (ComplexShape.up ℤ))
      (Z.obj.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q).symm ≪≫
    Functor.isoWhiskerRight eC.symm DerivedCategory.Q ≪≫
    Functor.associator (P.obj.mapHomologicalComplex (ComplexShape.up ℤ))
      (UC.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q
  let square := @Functor.rightDerivedDesc _ _ _ _ _ _
    (Functor.RightDerived.KInjective.functor P.obj ⋙
      Functor.RightDerived.KInjective.functor UC) _ _
    (eSource.hom ≫ Functor.RightDerived.Composition.iteratedUnit αP αUC)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) inferInstance
    (crystallinePushforwardAcyclic B f x'₀ h_over h_p' _ eSource)
    (Functor.RightDerived.KInjective.functor UD ⋙ Z.mapDerivedCategory)
    (Functor.RightDerived.Composition.iteratedUnit αUD αZ)
  let F' := (crystalPullback B f x'₀ h_over h_p').obj F
  let M := (SheafOfModules.toSheaf _).obj F'
  let η := (SheafOfModules.toSheaf _).map (r.moduleAdjunction.unit.app F) ≫
    (modulePushforwardAbelianComparison B f x'₀ h_over h_p').app F'
  let singleP :=
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex P.obj (ComplexShape.up ℤ) 0).app M)).inv ≫
    αP.app ((CochainComplex.singleFunctor _ 0).obj M)
  (Functor.RightDerived.KInjective.functor UC).map
      ((DerivedCategory.singleFunctor _ 0).map η) ≫
    (Functor.RightDerived.KInjective.functor UC).map singleP ≫
    square.app ((DerivedCategory.singleFunctor _ 0).obj M)

/-- The canonical crystalline coefficient comparison is natural in its module
coefficients. -/
theorem crystallineComparison_spec (hf : IsHomeomorph f)
    {F G : SheafOfModules.{u + 1} B.liftedStructureSheaf} (a : F ⟶ G) :
    (derivedSmallCrystallinePushforward.{u, u + 1, u + 1, u + 1, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
      B.sourceToClosed B.prime_nilpotent).map
        ((DerivedCategory.singleFunctor _ 0).map ((SheafOfModules.toSheaf _).map a)) ≫
      crystallineComparison B f x'₀ h_over h_p' hf G =
    crystallineComparison B f x'₀ h_over h_p' hf F ≫
      (zariskiAbelianPushforwardExact.{u, u + 1} f hf).mapDerivedCategory.map
        ((derivedSmallCrystallinePushforward.{u, u + 1, u + 1, u + 1, u + 1} B.ideal B.dividedPowers B.compatible B.toSpec
          x'₀ h_p').map ((DerivedCategory.singleFunctor _ 0).map
            ((SheafOfModules.toSheaf _).map
              ((crystalPullback B f x'₀ h_over h_p').map a)))) := sorry

end AlgebraicGeometry.Scheme.Crystalline
