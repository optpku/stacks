module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap75.Lemma_75_11_3_GlobalSections
public import stacks_project.Chap75.Lemma_75_19_1_Instances
public import stacks_project.Chap75.Lemma_75_20_1_ProjectionFormula
public import stacks_project.Chap77.Lemma_77_12_2_HomotopyLimit
public import stacks_project.Chap77.Lemma_77_12_3_Instances
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction

/-!
# Derived global sections and base-change comparisons for proper flat formal systems

In Situation 77.12.1, the quasi-coherent coreflection `K` of a homotopy limit of the
pushed stage sheaves is compared with the finite-level complexes `ℱ n` after derived
tensor and derived internal Hom against a perfect object of `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed CategoryTheory.Functor
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
  (modulesMonoidalCategory modulesMonoidalPreadditive
    modulesHasMapBifunctor hasDerivedTensorRight)
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open ComplexShape Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Recover a morphism of schemes over `S` from a morphism of the associated algebraic
spaces. -/
def ofOverHomPreimage {S : Scheme.{u}} {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage φ

/-- `ofOverHomPreimage φ` is the Yoneda preimage of `φ`. -/
theorem ofOverHomPreimage_eq {S : Scheme.{u}} {U V : Over S} (φ : ofOver U ⟶ ofOver V) :
    ofOverHomPreimage φ = Yoneda.fullyFaithful.preimage φ :=
  rfl

/-- The two presentation restrictions of `Y` agree after composing the `ΓSpec` adjunct of
`toSpecGamma` along `f`. -/
theorem globalSectionsRingMap_equalizes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
          ((ofOverHomPreimage
                ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
            specGamma_fst X).appTop) ≫
        (chosenPresentation Y).tAppTop =
      ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
          ((ofOverHomPreimage
                ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
            specGamma_fst X).appTop) ≫
        (chosenPresentation Y).sAppTop :=
  sorry

/-- The map on global sections `Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)` induced by a morphism of algebraic
spaces. -/
def globalSectionsRingMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ globalSectionsRing Y :=
  equalizer.lift
    ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
      ((ofOverHomPreimage
            ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
        specGamma_fst X).appTop)
    (globalSectionsRingMap_equalizes f)

/-- `globalSectionsRingMap f` lifts the `ΓSpec` adjunct of `Y → Spec Γ(X)` through the
equalizer inclusion of `Γ(Y, 𝒪_Y)`. -/
theorem globalSectionsRingMap_comp_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRingMap f ≫ globalSectionsRing_ι Y =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
        ((ofOverHomPreimage
              ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
          specGamma_fst X).appTop :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- Fixed-right derived tensor with a pinned Chap75 instance on an algebraic space. -/
abbrev tensorRightFunctor {R : Scheme.{u}} {Y : AlgebraicSpace R}
    (E : ModuleDerived Y) : ModuleDerived Y ⥤ ModuleDerived Y :=
  @DerivedTensor.Right.functor (Modules Y) _ _ _
    (modulesMonoidalCategory Y) (modulesMonoidalPreadditive Y)
    (modulesHasMapBifunctor Y) E (hasDerivedTensorRight Y)

/-- Evaluating `tensorRightFunctor E` is fixed-right derived tensor with right factor `E`. -/
theorem tensorRightFunctor_obj {R : Scheme.{u}} {Y : AlgebraicSpace R}
    (K E : ModuleDerived Y) :
    (tensorRightFunctor E).obj K =
      @DerivedTensor.Right.obj (Modules Y) _ _ _
        (modulesMonoidalCategory Y) (modulesMonoidalPreadditive Y)
        (modulesHasMapBifunctor Y) K E (hasDerivedTensorRight Y) :=
  sorry

/-- The inverse-limit ring `A` of a proper flat formal system. -/
abbrev limitRing (S : ProperFlatFormalSystem) : Type u := S.limitCone.cone.pt

/-- The finite-stage ring `A_n` of a proper flat formal system. -/
abbrev stageRing (S : ProperFlatFormalSystem) (n : ℕ) : Type u :=
  S.ringSystem.obj (Opposite.op n)

/-- The two presentation restrictions agree on the global-sections map of the atlas
structure morphism over the inverse-limit ring. -/
theorem limitRingToGlobalSections_equalizes (S : ProperFlatFormalSystem) :
    ((Scheme.ΓSpecIso S.limitCone.cone.pt).inv ≫
          (chosenPresentation S.space).U.hom.appTop) ≫
        (chosenPresentation S.space).tAppTop =
      ((Scheme.ΓSpecIso S.limitCone.cone.pt).inv ≫
          (chosenPresentation S.space).U.hom.appTop) ≫
        (chosenPresentation S.space).sAppTop :=
  sorry

/-- The structure morphism of the limit space induces `A →+* Γ(X, 𝒪_X)`. -/
def limitRingToGlobalSections (S : ProperFlatFormalSystem) :
    limitRing S →+* (globalSectionsRing S.space : Type u) :=
  (equalizer.lift
      ((Scheme.ΓSpecIso S.limitCone.cone.pt).inv ≫
        (chosenPresentation S.space).U.hom.appTop)
      (limitRingToGlobalSections_equalizes S)).hom

/-- `limitRingToGlobalSections` is the equalizer lift of the atlas structure map over
`Spec A`. -/
theorem limitRingToGlobalSections_eq (S : ProperFlatFormalSystem) :
    CommRingCat.ofHom (limitRingToGlobalSections S) =
      equalizer.lift
        ((Scheme.ΓSpecIso S.limitCone.cone.pt).inv ≫
          (chosenPresentation S.space).U.hom.appTop)
        (limitRingToGlobalSections_equalizes S) :=
  sorry

/-- The atlas of `X_n`, as a scheme over `Spec A_n`, obtained by composing the chosen
atlas of `X_n` with `stageToSpec n`. -/
def stageAtlasToSpec (S : ProperFlatFormalSystem) (n : ℕ) :
    (chosenPresentation (S.stageSpace n)).U ⟶
      Over.mk (Spec.map (S.limitCone.cone.stageMap n)) :=
  Yoneda.fullyFaithful.preimage
    ((chosenPresentation (S.stageSpace n)).atlas ≫ S.stageToSpec n)

/-- `stageAtlasToSpec` is the Yoneda preimage of the atlas composite with `stageToSpec`. -/
theorem stageAtlasToSpec_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    stageAtlasToSpec S n =
      Yoneda.fullyFaithful.preimage
        ((chosenPresentation (S.stageSpace n)).atlas ≫ S.stageToSpec n) :=
  rfl

/-- The two presentation restrictions of `X_n` agree after restriction from `Spec A_n`. -/
theorem stageRingToGlobalSections_equalizes (S : ProperFlatFormalSystem) (n : ℕ) :
    ((Scheme.ΓSpecIso (S.ringSystem.obj (Opposite.op n))).inv ≫
          (stageAtlasToSpec S n).left.appTop) ≫
        (chosenPresentation (S.stageSpace n)).tAppTop =
      ((Scheme.ΓSpecIso (S.ringSystem.obj (Opposite.op n))).inv ≫
          (stageAtlasToSpec S n).left.appTop) ≫
        (chosenPresentation (S.stageSpace n)).sAppTop :=
  sorry

/-- The structure morphism `X_n ⟶ Spec A_n` induces `A_n →+* Γ(X_n, 𝒪_{X_n})`. -/
def stageRingToGlobalSections (S : ProperFlatFormalSystem) (n : ℕ) :
    stageRing S n →+* (globalSectionsRing (S.stageSpace n) : Type u) :=
  (equalizer.lift
      ((Scheme.ΓSpecIso (S.ringSystem.obj (Opposite.op n))).inv ≫
        (stageAtlasToSpec S n).left.appTop)
      (stageRingToGlobalSections_equalizes S n)).hom

/-- `stageRingToGlobalSections` is the equalizer lift of the atlas map over `Spec A_n`. -/
theorem stageRingToGlobalSections_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    CommRingCat.ofHom (stageRingToGlobalSections S n) =
      equalizer.lift
        ((Scheme.ΓSpecIso (S.ringSystem.obj (Opposite.op n))).inv ≫
          (stageAtlasToSpec S n).left.appTop)
        (stageRingToGlobalSections_equalizes S n) :=
  sorry

/-- The quasi-coherent coreflection of an ambient homotopy limit of the pushed stage
sheaves, as an object of `D(𝒪_X)`. -/
def homotopyLimitCoherator (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space) :
    ModuleDerived S.space :=
  ((DerivedQCoh.inclusion S.space).rightAdjoint.obj Klim).obj

/-- `homotopyLimitCoherator` is the underlying object of the right adjoint of
`DerivedQCoh.inclusion` applied to the ambient homotopy limit. -/
theorem homotopyLimitCoherator_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space) :
    homotopyLimitCoherator S F Klim =
      ((DerivedQCoh.inclusion S.space).rightAdjoint.obj Klim).obj :=
  rfl

/-- Derived global sections of the limit space, regarded in `D(A)`. -/
def globalSectionsOverLimit (S : ProperFlatFormalSystem) :
    ModuleDerived S.space ⥤ DerivedCategory (ModuleCat.{u} (limitRing S)) :=
  moduleDerivedGlobalSections S.space ⋙
    ModuleCat.derivedRestrictionOfScalars.{u} (limitRingToGlobalSections S)

/-- `globalSectionsOverLimit` is `RΓ(X, -)` followed by restriction of scalars along
`A →+* Γ(X, 𝒪_X)`. -/
theorem globalSectionsOverLimit_eq (S : ProperFlatFormalSystem) :
    globalSectionsOverLimit S =
      moduleDerivedGlobalSections S.space ⋙
        ModuleCat.derivedRestrictionOfScalars.{u} (limitRingToGlobalSections S) :=
  rfl

/-- On objects, `globalSectionsOverLimit` is `RΓ(X, E)` viewed in `D(A)`. -/
theorem globalSectionsOverLimit_obj (S : ProperFlatFormalSystem) (E : ModuleDerived S.space) :
    (globalSectionsOverLimit S).obj E =
      (ModuleCat.derivedRestrictionOfScalars.{u} (limitRingToGlobalSections S)).obj
        ((moduleDerivedGlobalSections S.space).obj E) :=
  rfl

/-- Derived global sections of a finite-stage space, regarded in `D(A_n)`. -/
def globalSectionsOverStage (S : ProperFlatFormalSystem) (n : ℕ) :
    ModuleDerived (S.stageSpace n) ⥤
      DerivedCategory (ModuleCat.{u} (stageRing S n)) :=
  moduleDerivedGlobalSections (S.stageSpace n) ⋙
    ModuleCat.derivedRestrictionOfScalars.{u} (stageRingToGlobalSections S n)

/-- `globalSectionsOverStage` is `RΓ(X_n, -)` followed by restriction of scalars along
`A_n →+* Γ(X_n, 𝒪_{X_n})`. -/
theorem globalSectionsOverStage_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    globalSectionsOverStage S n =
      moduleDerivedGlobalSections (S.stageSpace n) ⋙
        ModuleCat.derivedRestrictionOfScalars.{u} (stageRingToGlobalSections S n) :=
  rfl

/-- On objects, `globalSectionsOverStage` is `RΓ(X_n, E)` viewed in `D(A_n)`. -/
theorem globalSectionsOverStage_obj (S : ProperFlatFormalSystem) (n : ℕ)
    (E : ModuleDerived (S.stageSpace n)) :
    (globalSectionsOverStage S n).obj E =
      (ModuleCat.derivedRestrictionOfScalars.{u} (stageRingToGlobalSections S n)).obj
        ((moduleDerivedGlobalSections (S.stageSpace n)).obj E) :=
  rfl

/-- The derived pullback of an object of `D(𝒪_X)` along `X_n ⟶ X`. -/
abbrev pullbackStage (S : ProperFlatFormalSystem) (n : ℕ) :
    ModuleDerived S.space ⥤ ModuleDerived (S.stageSpace n) :=
  modulePullbackDerived (S.stageToSpace n)

/-- `pullbackStage` is the unbounded derived pullback along the closed immersion `X_n ⟶ X`. -/
theorem pullbackStage_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    pullbackStage S n = modulePullbackDerived (S.stageToSpace n) :=
  rfl

/-- The stage module sheaf `ℱ n`, placed in degree zero in `D(𝒪_{X_n})`. -/
def stageSingle (S : ProperFlatFormalSystem) (n : ℕ) : ModuleDerived (S.stageSpace n) :=
  (DerivedCategory.singleFunctor (Modules (S.stageSpace n)) (0 : ℤ)).obj (S.moduleSheaf n)

/-- `stageSingle` is the degree-zero single complex on the stage module sheaf. -/
theorem stageSingle_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    stageSingle S n =
      (DerivedCategory.singleFunctor (Modules (S.stageSpace n)) (0 : ℤ)).obj
        (S.moduleSheaf n) :=
  rfl

/-- Derived tensor of the coherator of a homotopy limit against an object of `D(𝒪_X)`, as an
object of `D(A)`. -/
def globalSectionsTensor (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (E : ModuleDerived S.space) :
    DerivedCategory (ModuleCat.{u} (limitRing S)) :=
  (globalSectionsOverLimit S).obj
    ((tensorRightFunctor E).obj (homotopyLimitCoherator S F Klim))

/-- `globalSectionsTensor` is `RΓ(X, K ⊗ᴸ E)` viewed in `D(A)`. -/
theorem globalSectionsTensor_obj (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (E : ModuleDerived S.space) :
    globalSectionsTensor S F Klim E =
      (globalSectionsOverLimit S).obj
        ((tensorRightFunctor E).obj (homotopyLimitCoherator S F Klim)) :=
  rfl

/-- Derived tensor of a stage sheaf against the derived pullback of `E`, as an object of
`D(A_n)`. -/
def globalSectionsTensorStage (S : ProperFlatFormalSystem) (n : ℕ)
    (E : ModuleDerived S.space) :
    DerivedCategory (ModuleCat.{u} (stageRing S n)) :=
  (globalSectionsOverStage S n).obj
    ((tensorRightFunctor ((pullbackStage S n).obj E)).obj (stageSingle S n))

/-- `globalSectionsTensorStage` is `RΓ(X_n, ℱ n ⊗ᴸ E|_{X_n})` viewed in `D(A_n)`. -/
theorem globalSectionsTensorStage_obj (S : ProperFlatFormalSystem) (n : ℕ)
    (E : ModuleDerived S.space) :
    globalSectionsTensorStage S n E =
      (globalSectionsOverStage S n).obj
        ((tensorRightFunctor ((pullbackStage S n).obj E)).obj (stageSingle S n)) :=
  rfl

/-- Derived internal Hom from `E` into the coherator, as an object of `D(A)`. -/
def globalHom (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (H : MonoidalClosed (ModuleDerived S.space)) (E : ModuleDerived S.space) :
    DerivedCategory (ModuleCat.{u} (limitRing S)) :=
  (globalSectionsOverLimit S).obj ((ihomOf H E).obj (homotopyLimitCoherator S F Klim))

/-- `globalHom` is `RΓ(X, RHom(E, K))` viewed in `D(A)`. -/
theorem globalHom_obj (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (H : MonoidalClosed (ModuleDerived S.space)) (E : ModuleDerived S.space) :
    globalHom S F Klim H E =
      (globalSectionsOverLimit S).obj
        ((ihomOf H E).obj (homotopyLimitCoherator S F Klim)) :=
  rfl

/-- Derived internal Hom on a finite-stage space from the derived pullback of `E` into the
stage sheaf, as an object of `D(A_n)`. -/
def globalHomStage (S : ProperFlatFormalSystem) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) :
    DerivedCategory (ModuleCat.{u} (stageRing S n)) :=
  (globalSectionsOverStage S n).obj
    ((ihomOf H_n ((pullbackStage S n).obj E)).obj (stageSingle S n))

/-- `globalHomStage` is `RΓ(X_n, RHom(E|_{X_n}, ℱ n))` viewed in `D(A_n)`. -/
theorem globalHomStage_obj (S : ProperFlatFormalSystem) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) :
    globalHomStage S n H_n E =
      (globalSectionsOverStage S n).obj
        ((ihomOf H_n ((pullbackStage S n).obj E)).obj (stageSingle S n)) :=
  rfl

/-- The canonical comparison from the degree-zero pushforward of a stage sheaf to derived
pushforward of the corresponding single complex. -/
def singlePushforwardComparison (S : ProperFlatFormalSystem) (n : ℕ) :
    (DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)).obj (S.pushforwardModule n) ⟶
      (Modules.pushforwardDerived (S.stageToSpace n)).obj (stageSingle S n) :=
  (DerivedCategory.singleFunctorIsoCompQ (Modules S.space) (0 : ℤ)).hom.app
      (S.pushforwardModule n) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (Modules.pushforward (S.stageToSpace n)) (ComplexShape.up ℤ) (0 : ℤ)).inv.app
        (S.moduleSheaf n)) ≫
    (Modules.moduleDerivedPushforward.unit (S.stageToSpace n)).app
      ((CochainComplex.singleFunctor (Modules (S.stageSpace n)) (0 : ℤ)).obj
        (S.moduleSheaf n)) ≫
    (Modules.pushforwardDerived (S.stageToSpace n)).map
      ((DerivedCategory.singleFunctorIsoCompQ (Modules (S.stageSpace n)) (0 : ℤ)).inv.app
        (S.moduleSheaf n))

/-- `singlePushforwardComparison` is the single-complex identification followed by the
K-injective unit of derived pushforward. -/
theorem singlePushforwardComparison_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    singlePushforwardComparison S n =
      (DerivedCategory.singleFunctorIsoCompQ (Modules S.space) (0 : ℤ)).hom.app
          (S.pushforwardModule n) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
              (Modules.pushforward (S.stageToSpace n)) (ComplexShape.up ℤ) (0 : ℤ)).inv.app
            (S.moduleSheaf n)) ≫
        (Modules.moduleDerivedPushforward.unit (S.stageToSpace n)).app
          ((CochainComplex.singleFunctor (Modules (S.stageSpace n)) (0 : ℤ)).obj
            (S.moduleSheaf n)) ≫
        (Modules.pushforwardDerived (S.stageToSpace n)).map
          ((DerivedCategory.singleFunctorIsoCompQ (Modules (S.stageSpace n))
              (0 : ℤ)).inv.app (S.moduleSheaf n)) :=
  rfl

/-- The stage identification of a quasicoherent system, followed by the canonical
degree-zero comparison from ordinary to derived pushforward. -/
def thickeningSystemStageMap (S : ProperFlatFormalSystem)
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (n : ℕ) :
    ((F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)).obj
      (Opposite.op n)) ⟶
      (Modules.pushforwardDerived (S.stageToSpace n)).obj (stageSingle S n) :=
  (DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)).map (stageIso n).hom ≫
    singlePushforwardComparison S n

/-- `thickeningSystemStageMap` is the stage isomorphism followed by
`singlePushforwardComparison`. -/
theorem thickeningSystemStageMap_eq (S : ProperFlatFormalSystem)
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (n : ℕ) :
    thickeningSystemStageMap S F stageIso n =
      (DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)).map (stageIso n).hom ≫
        singlePushforwardComparison S n :=
  rfl


/-- The counit of the quasi-coherent coreflection applied to an ambient homotopy limit. -/
def coheratorCounit (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space) :
    homotopyLimitCoherator S F Klim ⟶ Klim :=
  (Adjunction.ofIsLeftAdjoint (DerivedQCoh.inclusion S.space)).counit.app Klim

/-- `coheratorCounit` is the counit of `DerivedQCoh.inclusion ⊣ rightAdjoint` at `Klim`. -/
theorem coheratorCounit_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space) :
    coheratorCounit S F Klim =
      (Adjunction.ofIsLeftAdjoint (DerivedQCoh.inclusion S.space)).counit.app Klim :=
  rfl

/-- The canonical map from a presented limit to a stage, followed by the identification
of that stage with a derived pushforward. -/
def limitToStagePushforward (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ) :
    homotopyLimitCoherator S F Klim ⟶
      (Modules.pushforwardDerived (S.stageToSpace n)).obj (stageSingle S n) :=
  coheratorCounit S F Klim ≫ P.stageProjection n ≫ thickeningSystemStageMap S F stageIso n

/-- `limitToStagePushforward` is the coreflection counit, the homotopy-limit stage
projection, and the stage identification. -/
theorem limitToStagePushforward_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ) :
    limitToStagePushforward S F stageIso Klim P n =
      coheratorCounit S F Klim ≫ P.stageProjection n ≫
        thickeningSystemStageMap S F stageIso n :=
  rfl

/-- Pulling the limit-to-stage map across the derived pullback-pushforward adjunction
gives the canonical comparison on the stage itself. -/
def pullbackLimitToStage (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ) :
    (modulePullbackDerived (S.stageToSpace n)).obj (homotopyLimitCoherator S F Klim) ⟶
      stageSingle S n :=
  ((modulePullbackDerivedPushforwardAdjunction (S.stageToSpace n)).homEquiv _ _).symm
    (limitToStagePushforward S F stageIso Klim P n)

/-- The adjunct of `pullbackLimitToStage` is `limitToStagePushforward`. -/
theorem pullbackLimitToStage_adjunct (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ) :
    (modulePullbackDerivedPushforwardAdjunction (S.stageToSpace n)).homEquiv _ _
        (pullbackLimitToStage S F stageIso Klim P n) =
      limitToStagePushforward S F stageIso Klim P n :=
  sorry

/-- Comparison of ordinary global sections of a pushforward with restricted global
sections on the source. -/
def pushforwardGlobalSectionsComparison {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) :
    Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X ⟶
      moduleGlobalSectionsFunctor Y ⋙
        ModuleCat.restrictScalars (globalSectionsRingMap f).hom where
  app G :=
    ConcreteCategory.ofHom
      ({
          toFun := fun x ↦
            (AddCommGrpCat.Hom.hom ((gammaPushforwardComparison f).app G)) x
          map_add' := fun _ _ ↦ sorry
          map_smul' := fun _ _ ↦ sorry
        } :
          (moduleGlobalSectionsFunctor X).obj ((Modules.pushforward f).obj G) →ₗ[globalSectionsRing X]
            (ModuleCat.restrictScalars (globalSectionsRingMap f).hom).obj
              ((moduleGlobalSectionsFunctor Y).obj G))
  naturality := fun _ _ _ ↦ sorry

/-- The component of `pushforwardGlobalSectionsComparison` is the abelian Leray comparison
on underlying additive groups, with the `Γ(X)`-action via `globalSectionsRingMap`. -/
theorem pushforwardGlobalSectionsComparison_app {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) (G : Y.Modules) :
    (forget₂ (ModuleCat.{u} (globalSectionsRing X)) AddCommGrpCat.{u}).map
        ((pushforwardGlobalSectionsComparison f).app G) =
      (gammaPushforwardComparison f).app G :=
  sorry

/-- Cochain-level iterated unit of `Rf_*` followed by `RΓ(X, -)`. -/
def derivedGlobalSectionsPushforwardCompositeUnit {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) :
    (Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
            DerivedCategory (ModuleCat.{u} (globalSectionsRing X))) ⟶
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
        (Modules.pushforwardDerived f ⋙ moduleDerivedGlobalSections X) :=
  whiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (Modules.pushforward f ⋙ moduleGlobalSectionsFunctor X)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator
      ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
      ((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X)))).hom ≫
    whiskerLeft ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsFunctor X)) ≫
    (Functor.associator
      ((Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)
      (moduleDerivedGlobalSections X)).inv ≫
    whiskerRight (Functor.RightDerived.KInjective.unit.{u} (Modules.pushforward f))
      (moduleDerivedGlobalSections X) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y)
      (Modules.pushforwardDerived f) (moduleDerivedGlobalSections X)).hom

/-- The composite `Rf_* ⋙ RΓ(X, -)` is a cochain-level right-derived model of
`Γ(X, f_* -)`. -/
instance derivedGlobalSectionsPushforwardComposite_isRightDerived
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (Modules.pushforwardDerived f ⋙ moduleDerivedGlobalSections X).IsRightDerivedFunctor
      (derivedGlobalSectionsPushforwardCompositeUnit f)
      (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
  sorry

/-- Cochain-level unit of `RΓ(Y, -)` followed by restriction of scalars along
`Γ(X) → Γ(Y)`. -/
def derivedGlobalSectionsRestrictUnit {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (moduleGlobalSectionsFunctor Y ⋙
        ModuleCat.restrictScalars (globalSectionsRingMap f).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X))) ⟶
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
        (moduleDerivedGlobalSections Y ⋙
          ModuleCat.derivedRestrictionOfScalars.{u} (globalSectionsRingMap f).hom) :=
  (Functor.associator
      ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
      ((ModuleCat.restrictScalars (globalSectionsRingMap f).hom).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing X)))).hom ≫
    whiskerLeft ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
      (ModuleCat.derivedRestrictionComplexUnit.{u} (globalSectionsRingMap f).hom) ≫
    (Functor.associator
      ((moduleGlobalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (ModuleCat.{u} (globalSectionsRing Y)) ℤ ⥤
          DerivedCategory (ModuleCat.{u} (globalSectionsRing Y)))
      (ModuleCat.derivedRestrictionOfScalars.{u} (globalSectionsRingMap f).hom)).inv ≫
    whiskerRight (Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsFunctor Y))
      (ModuleCat.derivedRestrictionOfScalars.{u} (globalSectionsRingMap f).hom) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y)
      (moduleDerivedGlobalSections Y)
      (ModuleCat.derivedRestrictionOfScalars.{u} (globalSectionsRingMap f).hom)).hom

/-- Canonical Leray map `RΓ(X, Rf_* K) ⟶ RΓ(Y, K)` after restriction of scalars along
`Γ(X) → Γ(Y)`. -/
def derivedGlobalSectionsPushforwardComparison {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) :
    Modules.pushforwardDerived f ⋙ moduleDerivedGlobalSections X ⟶
      moduleDerivedGlobalSections Y ⋙
        ModuleCat.derivedRestrictionOfScalars.{u} (globalSectionsRingMap f).hom :=
  (Modules.pushforwardDerived f ⋙ moduleDerivedGlobalSections X).rightDerivedDesc
    (derivedGlobalSectionsPushforwardCompositeUnit f)
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))
    (moduleDerivedGlobalSections Y ⋙
      ModuleCat.derivedRestrictionOfScalars.{u} (globalSectionsRingMap f).hom)
    (whiskerRight
        (NatTrans.mapHomologicalComplex (pushforwardGlobalSectionsComparison f) (ComplexShape.up ℤ))
        DerivedCategory.Q ≫
      derivedGlobalSectionsRestrictUnit f)

/-- A morphism `L ⟶ Rf_* K` induces the change-of-space map on derived global sections. -/
def globalSectionsMapOfPushforward {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    {K : ModuleDerived Y} {L : ModuleDerived X}
    (α : L ⟶ (Modules.pushforwardDerived f).obj K) :
    (moduleDerivedGlobalSections X).obj L ⟶
      (ModuleCat.derivedRestrictionOfScalars.{u} (globalSectionsRingMap f).hom).obj
        ((moduleDerivedGlobalSections Y).obj K) :=
  (moduleDerivedGlobalSections X).map α ≫
    (derivedGlobalSectionsPushforwardComparison f).app K

/-- `globalSectionsMapOfPushforward` is `RΓ(X, -)` of the given morphism, followed by the
Leray comparison. -/
theorem globalSectionsMapOfPushforward_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) {K : ModuleDerived Y} {L : ModuleDerived X}
    (α : L ⟶ (Modules.pushforwardDerived f).obj K) :
    globalSectionsMapOfPushforward f α =
      (moduleDerivedGlobalSections X).map α ≫
        (derivedGlobalSectionsPushforwardComparison f).app K :=
  rfl

/-- Compatibility of the two paths `A → Γ(X) → Γ(X_n)` and `A → A_n → Γ(X_n)`. -/
theorem stageRingToGlobalSections_comp (S : ProperFlatFormalSystem) (n : ℕ) :
    (stageRingToGlobalSections S n).comp (S.limitCone.cone.stageMap n).hom =
      (globalSectionsRingMap (S.stageToSpace n)).hom.comp
        (limitRingToGlobalSections S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
