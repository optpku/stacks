/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap75.Lemma_75_11_3_GlobalSections
public import stacks_project.Chap75.Lemma_75_20_1_ProjectionFormula
public import stacks_project.Chap75.Lemma_75_25_7_GlobalSections
public import stacks_project.Chap77.Lemma_77_13_2_Boundedness

/-!
# Derived global sections of a formal-completion homotopy limit after tensoring

In Situation 77.13.1, with `K` the quasi-coherent coreflection of a homotopy limit of
the pushforwards of the stages `K n`, this module owns `M = RΓ(X, K ⊗ᴸ E)` and the
canonical stage comparison in `D(A_n)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
  (modulesMonoidalCategory modulesMonoidalPreadditive
    modulesHasMapBifunctor hasDerivedTensorRight
    gammaPushforwardComparison)
open CategoryTheory.DerivedCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]

/-- Fixed-right derived tensor with a fixed right factor on an algebraic space. -/
noncomputable abbrev tensorRightFunctor {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (E : ModuleDerived Y) : ModuleDerived Y ⥤ ModuleDerived Y :=
  @DerivedTensor.Right.functor (Modules Y) _ _ _
    (modulesMonoidalCategory Y) (modulesMonoidalPreadditive Y)
    (modulesHasMapBifunctor Y) E (hasDerivedTensorRight Y)

/-- Evaluating `tensorRightFunctor E` is fixed-right derived tensor with right factor `E`. -/
theorem tensorRightFunctor_obj {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (K E : ModuleDerived Y) :
    (tensorRightFunctor E).obj K =
      @DerivedTensor.Right.obj (Modules Y) _ _ _
        (modulesMonoidalCategory Y) (modulesMonoidalPreadditive Y)
        (modulesHasMapBifunctor Y) K E (hasDerivedTensorRight Y) :=
  sorry


/-- The two presentation restrictions agree on the global-sections map of the chosen
atlas of an algebraic space over a bundled commutative ring. -/
theorem limitGlobalSectionsMap_equalizes {R : CommRingCat.{u}}
    (Y : AlgebraicSpace (Spec R)) :
    ((Scheme.ΓSpecIso R).inv ≫ (chosenPresentation Y).U.hom.appTop) ≫
        (chosenPresentation Y).tAppTop =
      ((Scheme.ΓSpecIso R).inv ≫ (chosenPresentation Y).U.hom.appTop) ≫
        (chosenPresentation Y).sAppTop :=
  sorry

/-- The structure morphism of an algebraic space over `Spec R` induces the ring map
`R →+* Γ(Y, 𝒪_Y)`. -/
noncomputable def limitGlobalSectionsMap {R : CommRingCat.{u}}
    (Y : AlgebraicSpace (Spec R)) :
    (R : Type u) →+* globalSectionsRing Y :=
  (equalizer.lift
      ((Scheme.ΓSpecIso R).inv ≫ (chosenPresentation Y).U.hom.appTop)
      (limitGlobalSectionsMap_equalizes Y)).hom

/-- `limitGlobalSectionsMap` is the equalizer lift of the atlas global-sections map
of the structure morphism to `Spec R`. -/
theorem limitGlobalSectionsMap_eq {R : CommRingCat.{u}}
    (Y : AlgebraicSpace (Spec R)) :
    limitGlobalSectionsMap Y =
      (equalizer.lift
          ((Scheme.ΓSpecIso R).inv ≫ (chosenPresentation Y).U.hom.appTop)
          (limitGlobalSectionsMap_equalizes Y)).hom :=
  sorry

/-- Derived global sections of an algebraic space over a bundled commutative ring,
as an object of `D(R)`. -/
noncomputable def limitGlobalSections {R : CommRingCat.{u}}
    (Y : AlgebraicSpace (Spec R)) :
    ModuleDerived Y ⥤ DerivedCategory (ModuleCat.{u} (R : Type u)) :=
  Modules.moduleDerivedGlobalSections Y ⋙
    ModuleCat.derivedRestrictionOfScalars (limitGlobalSectionsMap Y)

/-- On objects, `limitGlobalSections` is `RΓ(Y, E)` viewed in `D(R)`. -/
theorem limitGlobalSections_obj {R : CommRingCat.{u}}
    (Y : AlgebraicSpace (Spec R)) (E : ModuleDerived Y) :
    (limitGlobalSections Y).obj E =
      (ModuleCat.derivedRestrictionOfScalars (limitGlobalSectionsMap Y)).obj
        ((Modules.moduleDerivedGlobalSections Y).obj E) :=
  sorry

/-- The two presentation restrictions agree on the global-sections map of the chosen
atlas of `Spec(A_n)` as an algebraic space over `Spec A`. -/
theorem stageSpecGlobalSectionsMap_equalizes (n : ℕ) :
    ((Scheme.ΓSpecIso (A.obj (Opposite.op n))).inv ≫
          (Yoneda.fullyFaithful.preimage
            (chosenPresentation (Modules.stageSpec A_lim n)).atlas).left.appTop) ≫
        (chosenPresentation (Modules.stageSpec A_lim n)).tAppTop =
      ((Scheme.ΓSpecIso (A.obj (Opposite.op n))).inv ≫
          (Yoneda.fullyFaithful.preimage
            (chosenPresentation (Modules.stageSpec A_lim n)).atlas).left.appTop) ≫
        (chosenPresentation (Modules.stageSpec A_lim n)).sAppTop :=
  sorry

/-- The ring map `A_n →+* Γ(Spec A_n, 𝒪)` induced by viewing `Spec A_n` as an algebraic
space over `Spec A`. -/
noncomputable def stageSpecGlobalSectionsMap (n : ℕ) :
    (A.obj (Opposite.op n) : Type u) →+* globalSectionsRing (Modules.stageSpec A_lim n) :=
  (equalizer.lift
      ((Scheme.ΓSpecIso (A.obj (Opposite.op n))).inv ≫
        (Yoneda.fullyFaithful.preimage
          (chosenPresentation (Modules.stageSpec A_lim n)).atlas).left.appTop)
      (stageSpecGlobalSectionsMap_equalizes n)).hom

/-- `stageSpecGlobalSectionsMap` is the equalizer lift of the atlas global-sections
map of `Spec A_n`. -/
theorem stageSpecGlobalSectionsMap_eq (n : ℕ) :
    stageSpecGlobalSectionsMap n =
      (equalizer.lift
          ((Scheme.ΓSpecIso (A.obj (Opposite.op n))).inv ≫
            (Yoneda.fullyFaithful.preimage
              (chosenPresentation (Modules.stageSpec A_lim n)).atlas).left.appTop)
          (stageSpecGlobalSectionsMap_equalizes n)).hom :=
  sorry

/-- Recover a morphism of schemes over `S` from a morphism of the associated algebraic
spaces. -/
noncomputable def spaceOfOverHomPreimage {S : Scheme.{u}} {U V : Over S}
    (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage φ

/-- `spaceOfOverHomPreimage φ` is the Yoneda preimage of `φ`. -/
theorem spaceOfOverHomPreimage_eq {S : Scheme.{u}} {U V : Over S}
    (φ : ofOver U ⟶ ofOver V) :
    spaceOfOverHomPreimage φ = Yoneda.fullyFaithful.preimage φ :=
  sorry

/-- The two presentation restrictions of `Y` agree after composing the `ΓSpec` adjunct of
`toSpecGamma` along `f`. -/
theorem spaceGlobalSectionsRingMap_equalizes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
          ((spaceOfOverHomPreimage
                ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
            specGamma_fst X).appTop) ≫
        (chosenPresentation Y).tAppTop =
      ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
          ((spaceOfOverHomPreimage
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
      ((spaceOfOverHomPreimage
            ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
        specGamma_fst X).appTop)
    (spaceGlobalSectionsRingMap_equalizes f)

/-- `spaceGlobalSectionsRingMap f` lifts the `ΓSpec` adjunct of `Y → Spec Γ(X)` through the
equalizer inclusion of `Γ(Y, 𝒪_Y)`. -/
theorem spaceGlobalSectionsRingMap_comp_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    spaceGlobalSectionsRingMap f ≫ globalSectionsRing_ι Y =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
        ((spaceOfOverHomPreimage
              ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
          specGamma_fst X).appTop :=
  sorry

/-- Underived comparison of global sections of a pushforward, as modules over `Γ(X, 𝒪_X)`. -/
noncomputable def pushforwardGlobalSectionsComparison {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X ⟶
      moduleGlobalSectionsFunctor Y ⋙
        ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom where
  app G :=
    ConcreteCategory.ofHom
      ({
          toFun := fun x ↦
            (AddCommGrpCat.Hom.hom ((gammaPushforwardComparison f).app G)) x
          map_add' := fun _ _ ↦ sorry
          map_smul' := fun _ _ ↦ sorry
        } :
          (moduleGlobalSectionsFunctor X).obj ((Modules.pushforward f).obj G) →ₗ[globalSectionsRing X]
            (ModuleCat.restrictScalars (spaceGlobalSectionsRingMap f).hom).obj
              ((moduleGlobalSectionsFunctor Y).obj G))
  naturality := fun _ _ _ ↦ sorry

/-- The component of `pushforwardGlobalSectionsComparison` is the abelian Leray comparison
on underlying additive groups. -/
theorem pushforwardGlobalSectionsComparison_app {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) (G : Y.Modules) :
    (forget₂ (ModuleCat.{u} (globalSectionsRing X)) AddCommGrpCat.{u}).map
        ((pushforwardGlobalSectionsComparison f).app G) =
      (gammaPushforwardComparison f).app G :=
  sorry

/-- Cochain-level iterated unit of `Rf_*` followed by `RΓ(X, -)`. -/
noncomputable def derivedGlobalSectionsPushforwardCompositeUnit {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X))) ⟶
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
        (Modules.pushforwardDerived f ⋙ Modules.moduleDerivedGlobalSections X) :=
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
      (Modules.pushforwardDerived f) (Modules.moduleDerivedGlobalSections X)).hom

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
          (Modules.pushforwardDerived f) (Modules.moduleDerivedGlobalSections X)).hom :=
  sorry

/-- The composite `Rf_* ⋙ RΓ(X, -)` is a cochain-level right-derived model of
`Γ(X, f_* -)`. -/
instance derivedGlobalSectionsPushforwardComposite_isRightDerived
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (Modules.pushforwardDerived f ⋙ Modules.moduleDerivedGlobalSections X).IsRightDerivedFunctor
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
  sorry

/-- Canonical Leray map `RΓ(X, Rf_* K) ⟶ RΓ(Y, K)` after restriction of scalars along
`Γ(X) → Γ(Y)`. -/
noncomputable def derivedGlobalSectionsPushforwardComparison {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    Modules.pushforwardDerived f ⋙ Modules.moduleDerivedGlobalSections X ⟶
      Modules.moduleDerivedGlobalSections Y ⋙
        ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom :=
  (Modules.pushforwardDerived f ⋙ Modules.moduleDerivedGlobalSections X).rightDerivedDesc
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
      (Modules.pushforwardDerived f ⋙ Modules.moduleDerivedGlobalSections X).rightDerivedDesc
        (derivedGlobalSectionsPushforwardCompositeUnit f)
        (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))
        (Modules.moduleDerivedGlobalSections Y ⋙
          ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom)
        (Functor.whiskerRight
            (NatTrans.mapHomologicalComplex (pushforwardGlobalSectionsComparison f)
              (ComplexShape.up ℤ))
            DerivedCategory.Q ≫
          derivedGlobalSectionsRestrictUnit f) :=
  sorry

/-- A morphism `L ⟶ Rf_* K` induces the change-of-space map on derived global sections. -/
noncomputable def spaceGlobalSectionsMapOfPushforward {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    {K : ModuleDerived Y} {L : ModuleDerived X}
    (α : L ⟶ (Modules.pushforwardDerived f).obj K) :
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
    (α : L ⟶ (Modules.pushforwardDerived f).obj K) :
    spaceGlobalSectionsMapOfPushforward f α =
      (Modules.moduleDerivedGlobalSections X).map α ≫
        (derivedGlobalSectionsPushforwardComparison f).app K :=
  sorry

/-- The ring map `A_n →+* Γ(X_n, 𝒪)` obtained by viewing `X_n` over `Spec A_n` via `q n`. -/
noncomputable def stageSpaceGlobalSectionsMap
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ) :
    (A.obj (Opposite.op n) : Type u) →+* globalSectionsRing (Xn n) :=
  (spaceGlobalSectionsRingMap (q n)).hom.comp (stageSpecGlobalSectionsMap n)

/-- `stageSpaceGlobalSectionsMap` is the composite of `stageSpecGlobalSectionsMap` with the
map on global sections induced by `q n`. -/
theorem stageSpaceGlobalSectionsMap_eq
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ) :
    stageSpaceGlobalSectionsMap q n =
      (spaceGlobalSectionsRingMap (q n)).hom.comp (stageSpecGlobalSectionsMap n) :=
  sorry

/-- The two paths `A → A_n → Γ(X_n)` and `A → Γ(X) → Γ(X_n)` agree. -/
theorem stageSpaceGlobalSectionsMap_comp
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ) :
    (stageSpaceGlobalSectionsMap q n).comp (A_lim.cone.stageMap n).hom =
      (spaceGlobalSectionsRingMap (p n)).hom.comp (limitGlobalSectionsMap X) :=
  sorry

/-- Derived global sections of a finite-stage algebraic space, as an object of `D(A_n)`. -/
noncomputable def stageGlobalSections
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ) :
    ModuleDerived (Xn n) ⥤
      DerivedCategory (ModuleCat.{u} (A.obj (Opposite.op n) : Type u)) :=
  Modules.moduleDerivedGlobalSections (Xn n) ⋙
    ModuleCat.derivedRestrictionOfScalars (stageSpaceGlobalSectionsMap q n)

/-- On objects, `stageGlobalSections q n` is `RΓ(X_n, E)`, viewed in `D(A_n)`. -/
theorem stageGlobalSections_obj
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ)
    (E : ModuleDerived (Xn n)) :
    (stageGlobalSections q n).obj E =
      (ModuleCat.derivedRestrictionOfScalars (stageSpaceGlobalSectionsMap q n)).obj
        ((Modules.moduleDerivedGlobalSections (Xn n)).obj E) :=
  sorry

/-- The quasi-coherent coreflection of an ambient homotopy limit, as in Lemma 77.13.2. -/
noncomputable def coherator
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) : ModuleDerived X :=
  ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj

/-- `coherator Klim` is the underlying derived module of the right adjoint of
`DerivedQCoh.inclusion X` applied to `Klim`. -/
theorem coherator_obj
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) :
    coherator Klim = ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj :=
  sorry

/-- Derived global sections `M = RΓ(X, K ⊗ᴸ E)` over the limit ring, where `K` is the
quasi-coherent coreflection of the ambient homotopy limit `Klim`. -/
noncomputable def globalSectionsTensor
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) (E : ModuleDerived X) :
    DerivedCategory (ModuleCat.{u} (A_lim.cone.pt : Type u)) :=
  (limitGlobalSections X).obj
    ((tensorRightFunctor E).obj (coherator Klim))

/-- `globalSectionsTensor` is derived global sections of the derived tensor of the
coherator of `Klim` with `E`. -/
theorem globalSectionsTensor_obj
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) (E : ModuleDerived X) :
    globalSectionsTensor Klim E =
      (limitGlobalSections X).obj
        ((tensorRightFunctor E).obj
          ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj) :=
  sorry

/-- The canonical map from the coherator of a presented homotopy limit to the derived
pushforward of a stage complex. -/
noncomputable def coheratorToStagePushforward
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim) (n : ℕ) :
    coherator Klim ⟶ (Modules.pushforwardDerived (p n)).obj (S.K n) :=
  (Adjunction.ofIsLeftAdjoint (DerivedQCoh.inclusion X)).counit.app Klim ≫
    P.stageProjection n ≫ (stageIso n).hom

/-- `coheratorToStagePushforward` is the coherator counit, followed by the presented
stage projection and the stage identification with `R(p n)_* (S.K n)`. -/
theorem coheratorToStagePushforward_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim) (n : ℕ) :
    coheratorToStagePushforward S Ksys stageIso Klim P n =
      (Adjunction.ofIsLeftAdjoint (DerivedQCoh.inclusion X)).counit.app Klim ≫
        P.stageProjection n ≫ (stageIso n).hom :=
  sorry

/-- The geometric comparison `K ⊗ᴸ E ⟶ R(p n)_* (K_n ⊗ᴸ L(p n)^* E)` obtained by
tensoring the presented stage map and applying the projection-formula mate. -/
noncomputable def tensorToStagePushforward
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ) :
    (tensorRightFunctor E).obj (coherator Klim) ⟶
      (Modules.pushforwardDerived (p n)).obj
        ((tensorRightFunctor ((modulePullbackDerived (p n)).obj E)).obj (S.K n)) :=
  (tensorRightFunctor E).map
      (coheratorToStagePushforward S Ksys stageIso Klim P n) ≫
    leftMate (p n) (S.K n) E

/-- `tensorToStagePushforward` is the derived tensor of `coheratorToStagePushforward`
followed by the projection-formula mate `leftMate`. -/
theorem tensorToStagePushforward_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ) :
    tensorToStagePushforward S Ksys stageIso Klim P E n =
      (tensorRightFunctor E).map
          (coheratorToStagePushforward S Ksys stageIso Klim P n) ≫
        leftMate (p n) (S.K n) E :=
  sorry

/-- Derived global sections of `R(p n)_* (K_n ⊗ᴸ L(p n)^* E)` over the limit ring. -/
noncomputable def globalSectionsTensorStagePushforward
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (E : ModuleDerived X) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A_lim.cone.pt : Type u)) :=
  (limitGlobalSections X).obj
    ((Modules.pushforwardDerived (p n)).obj
      ((tensorRightFunctor ((modulePullbackDerived (p n)).obj E)).obj (S.K n)))

/-- The restriction-side comparison in `D(A)` induced by `tensorToStagePushforward`. -/
noncomputable def globalSectionsTensorRestrictionMap
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ) :
    globalSectionsTensor Klim E ⟶
      globalSectionsTensorStagePushforward S E n :=
  (limitGlobalSections X).map
    (tensorToStagePushforward S Ksys stageIso Klim P E n)

/-- `globalSectionsTensorRestrictionMap` is derived global sections of
`tensorToStagePushforward`. -/
theorem globalSectionsTensorRestrictionMap_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ) :
    globalSectionsTensorRestrictionMap S Ksys stageIso Klim P E n =
      (limitGlobalSections X).map
        (tensorToStagePushforward S Ksys stageIso Klim P E n) :=
  sorry

/-- `globalSectionsTensorStagePushforward` is derived global sections of the derived
pushforward of `K_n ⊗ᴸ L(p n)^* E`. -/
theorem globalSectionsTensorStagePushforward_obj
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (E : ModuleDerived X) (n : ℕ) :
    globalSectionsTensorStagePushforward S E n =
      (limitGlobalSections X).obj
        ((Modules.pushforwardDerived (p n)).obj
          ((tensorRightFunctor ((modulePullbackDerived (p n)).obj E)).obj (S.K n))) :=
  sorry

/-- Canonical Leray comparison from `RΓ(X, R(p n)_* G)` in `D(A)` to the restriction of
`RΓ(X_n, G)` along `A → A_n`. -/
noncomputable def pushforwardGlobalSectionsLeray
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ)
    (G : ModuleDerived (Xn n)) :
    (limitGlobalSections X).obj ((Modules.pushforwardDerived (p n)).obj G) ⟶
      (ModuleCat.derivedRestrictionOfScalars (A_lim.cone.stageMap n).hom).obj
        ((stageGlobalSections q n).obj G) :=
  (ModuleCat.derivedRestrictionOfScalars (limitGlobalSectionsMap X)).map
      (spaceGlobalSectionsMapOfPushforward (p n)
        (𝟙 ((Modules.pushforwardDerived (p n)).obj G))) ≫
    (ModuleCat.DerivedRestriction.compObjIso (limitGlobalSectionsMap X)
        (spaceGlobalSectionsRingMap (p n)).hom
        ((Modules.moduleDerivedGlobalSections (Xn n)).obj G)).inv ≫
    (ModuleCat.DerivedRestriction.compObjIsoOfEq (A_lim.cone.stageMap n).hom
        (stageSpaceGlobalSectionsMap q n)
        ((spaceGlobalSectionsRingMap (p n)).hom.comp (limitGlobalSectionsMap X))
        (stageSpaceGlobalSectionsMap_comp q n).symm
        ((Modules.moduleDerivedGlobalSections (Xn n)).obj G)).hom

/-- `pushforwardGlobalSectionsLeray` is restriction of the underived-space Leray map,
reassociated along `A → Γ(X) → Γ(X_n)` and `A → A_n → Γ(X_n)`. -/
theorem pushforwardGlobalSectionsLeray_def
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ)
    (G : ModuleDerived (Xn n)) :
    pushforwardGlobalSectionsLeray q n G =
      (ModuleCat.derivedRestrictionOfScalars (limitGlobalSectionsMap X)).map
          (spaceGlobalSectionsMapOfPushforward (p n)
            (𝟙 ((Modules.pushforwardDerived (p n)).obj G))) ≫
        (ModuleCat.DerivedRestriction.compObjIso (limitGlobalSectionsMap X)
            (spaceGlobalSectionsRingMap (p n)).hom
            ((Modules.moduleDerivedGlobalSections (Xn n)).obj G)).inv ≫
        (ModuleCat.DerivedRestriction.compObjIsoOfEq (A_lim.cone.stageMap n).hom
            (stageSpaceGlobalSectionsMap q n)
            ((spaceGlobalSectionsRingMap (p n)).hom.comp (limitGlobalSectionsMap X))
            (stageSpaceGlobalSectionsMap_comp q n).symm
            ((Modules.moduleDerivedGlobalSections (Xn n)).obj G)).hom :=
  sorry

/-- The canonical comparison `M ⊗ᴸ_A A_n ⟶ RΓ(X_n, K_n ⊗ᴸ L(p n)^* E)` in `D(A_n)`,
obtained by transposing the restriction-side composite of
`globalSectionsTensorRestrictionMap` with `pushforwardGlobalSectionsLeray`. -/
noncomputable def globalSectionsTensorBaseChangeMap
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    Ext.obj (globalSectionsTensor Klim E) ⟶
      (stageGlobalSections q n).obj
        ((tensorRightFunctor ((modulePullbackDerived (p n)).obj E)).obj (S.K n)) :=
  Ext.transpose
    (globalSectionsTensorRestrictionMap S Ksys stageIso Klim P E n ≫
      pushforwardGlobalSectionsLeray q n
        ((tensorRightFunctor ((modulePullbackDerived (p n)).obj E)).obj (S.K n)))

/-- `globalSectionsTensorBaseChangeMap` is the derived-extension transpose of the
restriction-side Leray composite of `globalSectionsTensorRestrictionMap`. -/
theorem globalSectionsTensorBaseChangeMap_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    globalSectionsTensorBaseChangeMap S Ksys stageIso Klim P E n Ext =
      Ext.transpose
        (globalSectionsTensorRestrictionMap S Ksys stageIso Klim P E n ≫
          pushforwardGlobalSectionsLeray q n
            ((tensorRightFunctor ((modulePullbackDerived (p n)).obj E)).obj
              (S.K n))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
