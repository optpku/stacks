/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction

/-! # Module-valued global sections and direct images -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules (gammaPushforwardComparison)
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The two presentation restrictions of `Y` agree after composing the `ΓSpec` adjunct of
`toSpecGamma` along `f`. -/
theorem spaceGlobalSectionsRingMap_equalizes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
          ((Yoneda.fullyFaithful.preimage
                ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
            specGamma_fst X).appTop) ≫
        (chosenPresentation Y).tAppTop =
      ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
          ((Yoneda.fullyFaithful.preimage
                ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
            specGamma_fst X).appTop) ≫
        (chosenPresentation Y).sAppTop :=
  sorry

/-- The map on global sections `Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)` induced by a morphism of algebraic
spaces. -/
noncomputable def spaceGlobalSectionsRingMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    globalSectionsRing X ⟶ globalSectionsRing Y :=
  equalizer.lift
    ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
      ((Yoneda.fullyFaithful.preimage
            ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
        specGamma_fst X).appTop)
    (spaceGlobalSectionsRingMap_equalizes f)

/-- `spaceGlobalSectionsRingMap f` lifts the `ΓSpec` adjunct of `Y → Spec Γ(X)` through the
equalizer inclusion of `Γ(Y, 𝒪_Y)`. -/
theorem spaceGlobalSectionsRingMap_comp_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    spaceGlobalSectionsRingMap f ≫ globalSectionsRing_ι Y =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
        ((Yoneda.fullyFaithful.preimage
              ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
          specGamma_fst X).appTop :=
  sorry

/-- The additive global-sections comparison respects the action of global functions. -/
theorem pushforwardGlobalSectionsComparison_smul {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) (G : Y.Modules) :
    let forward :
        (moduleGlobalSectionsFunctor X).obj ((Modules.pushforward f).obj G) →
          (ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom).obj
            ((moduleGlobalSectionsFunctor Y).obj G) :=
      fun x ↦ (AddCommGrpCat.Hom.hom ((gammaPushforwardComparison f).app G)) x
    ∀ (r : globalSectionsRing X)
      (x : (moduleGlobalSectionsFunctor X).obj ((Modules.pushforward f).obj G)),
      forward (r • x) = r • forward x :=
  sorry

/-- The global-sections comparison of a pushforward is linear over the target's global functions. -/
def pushforwardGlobalSectionsLinearMap {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) (G : Y.Modules) :
    (moduleGlobalSectionsFunctor X).obj ((Modules.pushforward f).obj G) →ₗ[globalSectionsRing X]
      (ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom).obj
        ((moduleGlobalSectionsFunctor Y).obj G) where
  toFun := (AddCommGrpCat.Hom.hom ((gammaPushforwardComparison f).app G))
  map_add' := (AddCommGrpCat.Hom.hom ((gammaPushforwardComparison f).app G)).map_add
  map_smul' := pushforwardGlobalSectionsComparison_smul f G

/-- The linear pushforward comparison commutes with morphisms of module sheaves. -/
theorem pushforwardGlobalSectionsLinearMap_naturality {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    let F := Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X
    let G := moduleGlobalSectionsFunctor Y ⋙
      ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom
    let η : ∀ M : Y.Modules, F.obj M ⟶ G.obj M := fun M ↦
      ModuleCat.ofHom (X := F.obj M) (Y := G.obj M)
        (pushforwardGlobalSectionsLinearMap f M)
    ∀ {M N : Y.Modules} (α : M ⟶ N), F.map α ≫ η N = η M ≫ G.map α :=
  sorry

/-- Global sections of a pushforward compare naturally with scalar-restricted global sections. -/
def pushforwardGlobalSectionsComparison {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X ⟶
      moduleGlobalSectionsFunctor Y ⋙
        ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom where
  app G := ModuleCat.ofHom
          (X := (moduleGlobalSectionsFunctor X).obj ((Modules.pushforward f).obj G))
          (Y := (ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom).obj
            ((moduleGlobalSectionsFunctor Y).obj G))
          (pushforwardGlobalSectionsLinearMap f G)
  naturality _ _ α := pushforwardGlobalSectionsLinearMap_naturality f α

/-- The component of `pushforwardGlobalSectionsComparison` is the abelian Leray comparison
on underlying additive groups. -/
theorem pushforwardGlobalSectionsComparison_app {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) (G : Y.Modules) :
    (forget₂ (ModuleCat.{u} (globalSectionsRing X)) AddCommGrpCat.{u}).map
        ((pushforwardGlobalSectionsComparison f).app G) =
      (gammaPushforwardComparison f).app G :=
  rfl

/-- Cochain-level iterated unit of `Rf_*` followed by `RΓ(X, -)`. -/
noncomputable def derivedGlobalSectionsPushforwardCompositeUnit {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X))) ⟶
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
        (Modules.moduleDerivedPushforward f ⋙ Modules.moduleDerivedGlobalSections X) :=
  Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X))
        (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator
      ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
      ((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X)))).hom ≫
    Functor.whiskerLeft ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsFunctor X)) ≫
    (Functor.associator
      ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)
      (Modules.moduleDerivedGlobalSections X)).inv ≫
    Functor.whiskerRight (Functor.RightDerived.KInjective.unit.{u} (Modules.pushforward f))
      (Modules.moduleDerivedGlobalSections X) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y)
      (Modules.moduleDerivedPushforward f) (Modules.moduleDerivedGlobalSections X)).hom

/-- `derivedGlobalSectionsPushforwardCompositeUnit` is the cochain-level iterated unit of
`Rf_*` followed by `RΓ(X, -)`. -/
theorem derivedGlobalSectionsPushforwardCompositeUnit_def {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    derivedGlobalSectionsPushforwardCompositeUnit f =
      Functor.whiskerRight
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X))
            (ComplexShape.up ℤ)).inv
          DerivedCategory.Q ≫
        (Functor.associator
          ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
          ((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
              DerivedCategory (ModuleCat.{u} (globalSectionsRing X)))).hom ≫
        Functor.whiskerLeft ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsFunctor X)) ≫
        (Functor.associator
          ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)
          (Modules.moduleDerivedGlobalSections X)).inv ≫
        Functor.whiskerRight (Functor.RightDerived.KInjective.unit.{u} (Modules.pushforward f))
          (Modules.moduleDerivedGlobalSections X) ≫
        (Functor.associator
          (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y)
          (Modules.moduleDerivedPushforward f) (Modules.moduleDerivedGlobalSections X)).hom :=
  rfl

/-- The composite `Rf_* ⋙ RΓ(X, -)` is a cochain-level right-derived model of
`Γ(X, f_* -)`. -/
instance derivedGlobalSectionsPushforwardComposite_isRightDerived
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (Modules.moduleDerivedPushforward f ⋙ Modules.moduleDerivedGlobalSections X).IsRightDerivedFunctor
      (derivedGlobalSectionsPushforwardCompositeUnit f)
      (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
  sorry

/-- Cochain-level unit of `RΓ(Y, -)` followed by restriction of scalars along
`Γ(X) → Γ(Y)`. -/
noncomputable def derivedGlobalSectionsRestrictUnit {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (moduleGlobalSectionsFunctor Y ⋙
        ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X))) ⟶
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
        (Modules.moduleDerivedGlobalSections Y ⋙
          ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom) :=
  (Functor.associator
      ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
      ((ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X)))).hom ≫
    Functor.whiskerLeft ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
      (ModuleCat.derivedRestrictionComplexUnit (spaceGlobalSectionsRingMap f).hom) ≫
    (Functor.associator
      ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing Y)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing Y)))
      (ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom)).inv ≫
    Functor.whiskerRight
      (Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsFunctor Y))
      (ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y)
      (Modules.moduleDerivedGlobalSections Y)
      (ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom)).hom

/-- `derivedGlobalSectionsRestrictUnit` is the cochain unit of derived global sections after
restriction of scalars along `spaceGlobalSectionsRingMap`. -/
theorem derivedGlobalSectionsRestrictUnit_def {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    derivedGlobalSectionsRestrictUnit f =
      (Functor.associator
          ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
          ((ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom).mapHomologicalComplex
            (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
              DerivedCategory (ModuleCat.{u} (globalSectionsRing X)))).hom ≫
        Functor.whiskerLeft
          ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
          (ModuleCat.derivedRestrictionComplexUnit (spaceGlobalSectionsRingMap f).hom) ≫
        (Functor.associator
          ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q :
            CochainComplex (ModuleCat.{u} (globalSectionsRing Y)) ℤ ⥤
              DerivedCategory (ModuleCat.{u} (globalSectionsRing Y)))
          (ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom)).inv ≫
        Functor.whiskerRight
          (Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsFunctor Y))
          (ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom) ≫
        (Functor.associator
          (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y)
          (Modules.moduleDerivedGlobalSections Y)
          (ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom)).hom :=
  rfl

/-- Canonical Leray map `RΓ(X, Rf_* K) ⟶ RΓ(Y, K)` after restriction of scalars along
`Γ(X) → Γ(Y)`. -/
noncomputable def derivedGlobalSectionsPushforwardComparison {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    Modules.moduleDerivedPushforward f ⋙ Modules.moduleDerivedGlobalSections X ⟶
      Modules.moduleDerivedGlobalSections Y ⋙
        ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom :=
  (Modules.moduleDerivedPushforward f ⋙ Modules.moduleDerivedGlobalSections X).rightDerivedDesc
    (derivedGlobalSectionsPushforwardCompositeUnit f)
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))
    (Modules.moduleDerivedGlobalSections Y ⋙
      ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom)
    (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (pushforwardGlobalSectionsComparison f)
          (ComplexShape.up ℤ))
        DerivedCategory.Q ≫
      derivedGlobalSectionsRestrictUnit f)

/-- `derivedGlobalSectionsPushforwardComparison` is right-derived descent of the underived
pushforward comparison along the composite unit. -/
theorem derivedGlobalSectionsPushforwardComparison_def {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    derivedGlobalSectionsPushforwardComparison f =
      (Modules.moduleDerivedPushforward f ⋙ Modules.moduleDerivedGlobalSections X).rightDerivedDesc
        (derivedGlobalSectionsPushforwardCompositeUnit f)
        (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))
        (Modules.moduleDerivedGlobalSections Y ⋙
          ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom)
        (Functor.whiskerRight
            (NatTrans.mapHomologicalComplex (pushforwardGlobalSectionsComparison f)
              (ComplexShape.up ℤ))
            DerivedCategory.Q ≫
          derivedGlobalSectionsRestrictUnit f) :=
  rfl

/-- A morphism `L ⟶ Rf_* K` induces the change-of-space map on derived global sections. -/
noncomputable def spaceGlobalSectionsMapOfPushforward {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    {K : ModuleDerived Y} {L : ModuleDerived X}
    (α : L ⟶ (Modules.moduleDerivedPushforward f).obj K) :
    (Modules.moduleDerivedGlobalSections X).obj L ⟶
      (ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom).obj
        ((Modules.moduleDerivedGlobalSections Y).obj K) :=
  (Modules.moduleDerivedGlobalSections X).map α ≫
    (derivedGlobalSectionsPushforwardComparison f).app K

/-- `spaceGlobalSectionsMapOfPushforward` is `RΓ(X, -)` of the given morphism, followed by
the Leray comparison. -/
theorem spaceGlobalSectionsMapOfPushforward_eq {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    {K : ModuleDerived Y} {L : ModuleDerived X}
    (α : L ⟶ (Modules.moduleDerivedPushforward f).obj K) :
    spaceGlobalSectionsMapOfPushforward f α =
      (Modules.moduleDerivedGlobalSections X).map α ≫
        (derivedGlobalSectionsPushforwardComparison f).app K :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
