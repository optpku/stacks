/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.MapToAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition

/-! # Derived objects and stage comparisons of proper flat formal systems -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.DerivedCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open ComplexShape Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The inverse-limit ring `A` of a proper flat formal system. -/
abbrev limitRing (S : ProperFlatFormalSystem) : Type u := S.limitCone.cone.pt

/-- The finite-stage ring `A_n` of a proper flat formal system. -/
abbrev stageRing (S : ProperFlatFormalSystem) (n : ℕ) : Type u :=
  S.ringSystem.obj (Opposite.op n)

/-- The structural morphism of the limit space induces its coefficient homomorphism. -/
def limitRingToGlobalSections (S : ProperFlatFormalSystem) :
    limitRing S →+* (globalSectionsRing S.space : Type u) :=
  (Hom.affineGlobalSectionsMap (SchemeRealization.toBase S.space)).hom

/-- The limit coefficient homomorphism is induced by the structural morphism to its affine base. -/
theorem limitRingToGlobalSections_eq (S : ProperFlatFormalSystem) :
    CommRingCat.ofHom (limitRingToGlobalSections S) =
      Hom.affineGlobalSectionsMap (SchemeRealization.toBase S.space) :=
  rfl

/-- The structural morphism of a finite stage induces its coefficient homomorphism. -/
def stageRingToGlobalSections (S : ProperFlatFormalSystem) (n : ℕ) :
    stageRing S n →+* (globalSectionsRing (S.stageSpace n) : Type u) :=
  (Hom.affineGlobalSectionsMap (S.stageToSpec n)).hom

/-- The stage coefficient homomorphism is induced by the structural morphism to its affine base. -/
theorem stageRingToGlobalSections_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    CommRingCat.ofHom (stageRingToGlobalSections S n) =
      Hom.affineGlobalSectionsMap (S.stageToSpec n) :=
  rfl

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
  ModuleDerived.pullback (S.stageToSpace n)

/-- `pullbackStage` is the unbounded derived pullback along the closed immersion `X_n ⟶ X`. -/
theorem pullbackStage_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    pullbackStage S n = ModuleDerived.pullback (S.stageToSpace n) :=
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
    ((DerivedTensor.Right.functor E).obj (homotopyLimitCoherator S F Klim))

/-- `globalSectionsTensor` is `RΓ(X, K ⊗ᴸ E)` viewed in `D(A)`. -/
theorem globalSectionsTensor_obj (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (E : ModuleDerived S.space) :
    globalSectionsTensor S F Klim E =
      (globalSectionsOverLimit S).obj
        ((DerivedTensor.Right.functor E).obj (homotopyLimitCoherator S F Klim)) :=
  rfl

/-- Derived tensor of a stage sheaf against the derived pullback of `E`, as an object of
`D(A_n)`. -/
def globalSectionsTensorStage (S : ProperFlatFormalSystem) (n : ℕ)
    (E : ModuleDerived S.space) :
    DerivedCategory (ModuleCat.{u} (stageRing S n)) :=
  (globalSectionsOverStage S n).obj
    ((DerivedTensor.Right.functor ((pullbackStage S n).obj E)).obj (stageSingle S n))

/-- `globalSectionsTensorStage` is `RΓ(X_n, ℱ n ⊗ᴸ E|_{X_n})` viewed in `D(A_n)`. -/
theorem globalSectionsTensorStage_obj (S : ProperFlatFormalSystem) (n : ℕ)
    (E : ModuleDerived S.space) :
    globalSectionsTensorStage S n E =
      (globalSectionsOverStage S n).obj
        ((DerivedTensor.Right.functor ((pullbackStage S n).obj E)).obj (stageSingle S n)) :=
  rfl

/-- Derived internal Hom from `E` into the coherator, as an object of `D(A)`. -/
def globalHom (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (E : ModuleDerived S.space) :
    DerivedCategory (ModuleCat.{u} (limitRing S)) :=
  (globalSectionsOverLimit S).obj ((ModuleDerived.InternalHom.functor E).obj (homotopyLimitCoherator S F Klim))

/-- `globalHom` is `RΓ(X, RHom(E, K))` viewed in `D(A)`. -/
theorem globalHom_obj (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    (E : ModuleDerived S.space) :
    globalHom S F Klim E =
      (globalSectionsOverLimit S).obj
        ((ModuleDerived.InternalHom.functor E).obj (homotopyLimitCoherator S F Klim)) :=
  rfl

/-- Derived internal Hom on a finite-stage space from the derived pullback of `E` into the
stage sheaf, as an object of `D(A_n)`. -/
def globalHomStage (S : ProperFlatFormalSystem) (n : ℕ)
    (E : ModuleDerived S.space) :
    DerivedCategory (ModuleCat.{u} (stageRing S n)) :=
  (globalSectionsOverStage S n).obj
    ((ModuleDerived.InternalHom.functor ((pullbackStage S n).obj E)).obj (stageSingle S n))

/-- `globalHomStage` is `RΓ(X_n, RHom(E|_{X_n}, ℱ n))` viewed in `D(A_n)`. -/
theorem globalHomStage_obj (S : ProperFlatFormalSystem) (n : ℕ)
    (E : ModuleDerived S.space) :
    globalHomStage S n E =
      (globalSectionsOverStage S n).obj
        ((ModuleDerived.InternalHom.functor ((pullbackStage S n).obj E)).obj (stageSingle S n)) :=
  rfl

/-- The canonical comparison from the degree-zero pushforward of a stage sheaf to derived
pushforward of the corresponding single complex. -/
def singlePushforwardComparison (S : ProperFlatFormalSystem) (n : ℕ) :
    (DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)).obj (S.pushforwardModule n) ⟶
      (Modules.moduleDerivedPushforward (S.stageToSpace n)).obj (stageSingle S n) :=
  (DerivedCategory.singleFunctorIsoCompQ (Modules S.space) (0 : ℤ)).hom.app
      (S.pushforwardModule n) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (Modules.pushforward (S.stageToSpace n)) (ComplexShape.up ℤ) (0 : ℤ)).inv.app
        (S.moduleSheaf n)) ≫
    (Modules.moduleDerivedPushforward.unit (S.stageToSpace n)).app
      ((CochainComplex.singleFunctor (Modules (S.stageSpace n)) (0 : ℤ)).obj
        (S.moduleSheaf n)) ≫
    (Modules.moduleDerivedPushforward (S.stageToSpace n)).map
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
        (Modules.moduleDerivedPushforward (S.stageToSpace n)).map
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
      (Modules.moduleDerivedPushforward (S.stageToSpace n)).obj (stageSingle S n) :=
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
      (Modules.moduleDerivedPushforward (S.stageToSpace n)).obj (stageSingle S n) :=
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
    (ModuleDerived.pullback (S.stageToSpace n)).obj (homotopyLimitCoherator S F Klim) ⟶
      stageSingle S n :=
  ((AlgebraicSpace.derivedPullbackPushforwardAdjunction (S.stageToSpace n)).homEquiv _ _).symm
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
    (AlgebraicSpace.derivedPullbackPushforwardAdjunction (S.stageToSpace n)).homEquiv _ _
        (pullbackLimitToStage S F stageIso Klim P n) =
      limitToStagePushforward S F stageIso Klim P n :=
  Equiv.apply_symm_apply _ _

/-- Compatibility of the two paths `A → Γ(X) → Γ(X_n)` and `A → A_n → Γ(X_n)`. -/
theorem stageRingToGlobalSections_comp (S : ProperFlatFormalSystem) (n : ℕ) :
    (stageRingToGlobalSections S n).comp (S.limitCone.cone.stageMap n).hom =
      (spaceGlobalSectionsRingMap (S.stageToSpace n)).hom.comp
        (limitRingToGlobalSections S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
