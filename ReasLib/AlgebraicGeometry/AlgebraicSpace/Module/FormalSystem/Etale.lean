/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition

/-! # Étale base change for derived global sections of formal systems

The canonical comparison for a formal system is obtained from the cartesian
base-change mate, coefficient restriction, and derived scalar extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory.DerivedCategory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- Derived global sections `RΓ(U, -)` over the inverse-limit ring, via restriction of
scalars along `A → Γ(X) → Γ(U)`. -/
def etaleGlobalSectionsOver (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) :
    ModuleDerived U ⥤ DerivedCategory (ModuleCat.{u} (limitRing S)) :=
  moduleDerivedGlobalSections U ⋙
    ModuleCat.derivedRestrictionOfScalars.{u}
      ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))

/-- On objects, `etaleGlobalSectionsOver S f` is `RΓ(U, E)` viewed in `D(A)`. -/
theorem etaleGlobalSectionsOver_obj (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space)
    (E : ModuleDerived U) :
    (etaleGlobalSectionsOver S f).obj E =
      (ModuleCat.derivedRestrictionOfScalars.{u}
          ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))).obj
        ((moduleDerivedGlobalSections U).obj E) :=
  rfl

/-- Derived global sections `RΓ(U, K)` over the inverse-limit ring, where `K` is the
quasi-coherent coreflection of the ambient homotopy limit `Klim` and the restriction
to `U` is derived pullback along `f`. -/
def etaleGlobalSections (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) :
    DerivedCategory (ModuleCat.{u} (limitRing S)) :=
  (etaleGlobalSectionsOver S f).obj
    ((modulePullbackDerived f).obj (homotopyLimitCoherator S F Klim))

/-- `etaleGlobalSections` is derived global sections of the derived pullback of
`homotopyLimitCoherator` along `f`. -/
theorem etaleGlobalSections_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space)) (Klim : ModuleDerived S.space)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) :
    etaleGlobalSections S F Klim f =
      (etaleGlobalSectionsOver S f).obj
        ((modulePullbackDerived f).obj (homotopyLimitCoherator S F Klim)) :=
  rfl

/-- The ring map `A_n →+* Γ(U_n, 𝒪)` obtained by composing `A_n → Γ(X_n)` with the map
on global sections induced by `U_n ⟶ X_n`. -/
def etaleStageRingToGlobalSections (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    stageRing S n →+* (globalSectionsRing (Limits.pullback f (S.stageToSpace n)) : Type u) :=
  (spaceGlobalSectionsRingMap (Limits.pullback.snd f (S.stageToSpace n))).hom.comp
    (stageRingToGlobalSections S n)

/-- `etaleStageRingToGlobalSections` is the composite of `stageRingToGlobalSections`
with the map on global sections induced by the projection `U_n ⟶ X_n`. -/
theorem etaleStageRingToGlobalSections_eq (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    etaleStageRingToGlobalSections S f n =
      (spaceGlobalSectionsRingMap (Limits.pullback.snd f (S.stageToSpace n))).hom.comp
        (stageRingToGlobalSections S n) :=
  rfl

/-- The two paths `A → A_n → Γ(U_n)` and `A → Γ(U) → Γ(U_n)` agree. -/
theorem etaleStageRingToGlobalSections_comp (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    (etaleStageRingToGlobalSections S f n).comp (S.limitCone.cone.stageMap n).hom =
      (spaceGlobalSectionsRingMap (Limits.pullback.fst f (S.stageToSpace n))).hom.comp
        ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S)) :=
  sorry

/-- Derived global sections of a finite-stage fibre product, as a functor to `D(A_n)`. -/
def etaleStageGlobalSections (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    ModuleDerived (Limits.pullback f (S.stageToSpace n)) ⥤
      DerivedCategory (ModuleCat.{u} (stageRing S n)) :=
  moduleDerivedGlobalSections (Limits.pullback f (S.stageToSpace n)) ⋙
    ModuleCat.derivedRestrictionOfScalars.{u} (etaleStageRingToGlobalSections S f n)

/-- On objects, `etaleStageGlobalSections S f n` is `RΓ(U_n, E)`, viewed in `D(A_n)`. -/
theorem etaleStageGlobalSections_obj (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    (E : ModuleDerived (Limits.pullback f (S.stageToSpace n))) :
    (etaleStageGlobalSections S f n).obj E =
      (ModuleCat.derivedRestrictionOfScalars.{u}
          (etaleStageRingToGlobalSections S f n)).obj
        ((moduleDerivedGlobalSections (Limits.pullback f (S.stageToSpace n))).obj E) :=
  rfl

/-- The geometric comparison `L f^* K ⟶ R(fst)_* L(snd)^* (ℱ n)` obtained by
derived-pulling back the presented stage map and applying the cartesian derived
base-change mate on `U_n = U ×_X X_n`. -/
def etaleCoheratorToStage (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    (modulePullbackDerived f).obj (homotopyLimitCoherator S F Klim) ⟶
      (Modules.moduleDerivedPushforward (Limits.pullback.fst f (S.stageToSpace n))).obj
        ((modulePullbackDerived (Limits.pullback.snd f (S.stageToSpace n))).obj (stageSingle S n)) :=
  (modulePullbackDerived f).map (limitToStagePushforward S F stageIso Klim P n) ≫
    Hom.DerivedBaseChange.app
      (IsPullback.of_hasPullback f (S.stageToSpace n)).flip.toCommSq (stageSingle S n)

/-- Canonical Leray comparison from `RΓ(U, R(fst)_* G)` in `D(A)` to the restriction of
`RΓ(U_n, G)` along `A → A_n`. -/
def etalePushforwardGlobalSectionsLeray (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    (G : ModuleDerived (Limits.pullback f (S.stageToSpace n))) :
    (etaleGlobalSectionsOver S f).obj
        ((Modules.moduleDerivedPushforward (Limits.pullback.fst f (S.stageToSpace n))).obj G) ⟶
      (ModuleCat.derivedRestrictionOfScalars.{u}
          (S.limitCone.cone.stageMap n).hom).obj
        ((etaleStageGlobalSections S f n).obj G) :=
  (ModuleCat.derivedRestrictionOfScalars.{u}
        ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))).map
      (spaceGlobalSectionsMapOfPushforward (Limits.pullback.fst f (S.stageToSpace n))
        (𝟙 ((Modules.moduleDerivedPushforward (Limits.pullback.fst f (S.stageToSpace n))).obj G))) ≫
    (ModuleCat.DerivedRestriction.compObjIso
        ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))
        (spaceGlobalSectionsRingMap (Limits.pullback.fst f (S.stageToSpace n))).hom
        ((moduleDerivedGlobalSections (Limits.pullback f (S.stageToSpace n))).obj G)).inv ≫
    (ModuleCat.DerivedRestriction.compObjIsoOfEq
        (S.limitCone.cone.stageMap n).hom (etaleStageRingToGlobalSections S f n)
        ((spaceGlobalSectionsRingMap (Limits.pullback.fst f (S.stageToSpace n))).hom.comp
          ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S)))
        (etaleStageRingToGlobalSections_comp S f n).symm
        ((moduleDerivedGlobalSections (Limits.pullback f (S.stageToSpace n))).obj G)).hom

/-- `etalePushforwardGlobalSectionsLeray` is restriction of the underived-space Leray
map, reassociated along `A → Γ(U) → Γ(U_n)` and `A → A_n → Γ(U_n)`. -/
theorem etalePushforwardGlobalSectionsLeray_eq (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    (G : ModuleDerived (Limits.pullback f (S.stageToSpace n))) :
    etalePushforwardGlobalSectionsLeray S f n G =
      (ModuleCat.derivedRestrictionOfScalars.{u}
            ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))).map
          (spaceGlobalSectionsMapOfPushforward (Limits.pullback.fst f (S.stageToSpace n))
            (𝟙 ((Modules.moduleDerivedPushforward (Limits.pullback.fst f (S.stageToSpace n))).obj G))) ≫
        (ModuleCat.DerivedRestriction.compObjIso
            ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))
            (spaceGlobalSectionsRingMap (Limits.pullback.fst f (S.stageToSpace n))).hom
            ((moduleDerivedGlobalSections (Limits.pullback f (S.stageToSpace n))).obj G)).inv ≫
        (ModuleCat.DerivedRestriction.compObjIsoOfEq
            (S.limitCone.cone.stageMap n).hom (etaleStageRingToGlobalSections S f n)
            ((spaceGlobalSectionsRingMap (Limits.pullback.fst f (S.stageToSpace n))).hom.comp
              ((spaceGlobalSectionsRingMap f).hom.comp (limitRingToGlobalSections S)))
            (etaleStageRingToGlobalSections_comp S f n).symm
            ((moduleDerivedGlobalSections (Limits.pullback f (S.stageToSpace n))).obj G)).hom :=
  rfl

/-- The restriction-side comparison in `D(A)` induced by `etaleCoheratorToStage`,
followed by the Leray reassociation to the restriction of `RΓ(U_n, ℱ n)`. -/
def etaleGlobalSectionsRestrictionMap (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    etaleGlobalSections S F Klim f ⟶
      (ModuleCat.derivedRestrictionOfScalars.{u}
          (S.limitCone.cone.stageMap n).hom).obj
        ((etaleStageGlobalSections S f n).obj
          ((modulePullbackDerived (Limits.pullback.snd f (S.stageToSpace n))).obj (stageSingle S n))) :=
  (etaleGlobalSectionsOver S f).map (etaleCoheratorToStage S F stageIso Klim P f n) ≫
    etalePushforwardGlobalSectionsLeray S f n
      ((modulePullbackDerived (Limits.pullback.snd f (S.stageToSpace n))).obj (stageSingle S n))

/-- `etaleGlobalSectionsRestrictionMap` is derived global sections of
`etaleCoheratorToStage`, followed by `etalePushforwardGlobalSectionsLeray`. -/
theorem etaleGlobalSectionsRestrictionMap_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    etaleGlobalSectionsRestrictionMap S F stageIso Klim P f n =
      (etaleGlobalSectionsOver S f).map
          (etaleCoheratorToStage S F stageIso Klim P f n) ≫
        etalePushforwardGlobalSectionsLeray S f n
          ((modulePullbackDerived (Limits.pullback.snd f (S.stageToSpace n))).obj (stageSingle S n)) :=
  rfl

/-- The canonical comparison `RΓ(U, K) ⊗ᴸ_A A_n ⟶ RΓ(U_n, ℱ n)` in `D(A_n)`, obtained
by transposing `etaleGlobalSectionsRestrictionMap`. -/
def etaleGlobalSectionsBaseChangeMap (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    Ext.obj (etaleGlobalSections S F Klim f) ⟶
      (etaleStageGlobalSections S f n).obj
        ((modulePullbackDerived (Limits.pullback.snd f (S.stageToSpace n))).obj (stageSingle S n)) :=
  Ext.transpose (etaleGlobalSectionsRestrictionMap S F stageIso Klim P f n)

/-- `etaleGlobalSectionsBaseChangeMap` is the derived-extension transpose of
`etaleGlobalSectionsRestrictionMap`. -/
theorem etaleGlobalSectionsBaseChangeMap_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    etaleGlobalSectionsBaseChangeMap S F stageIso Klim P f n Ext =
      Ext.transpose (etaleGlobalSectionsRestrictionMap S F stageIso Klim P f n) :=
  rfl

/-- For an étale morphism with quasi-compact quasi-separated source, the canonical
scalar-extension comparison from derived global sections of the quasi-coherent
homotopy limit to derived global sections of each finite stage is invertible. -/
theorem etaleGlobalSectionsBaseChangeMap_isIso (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardStep S n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space)
    [Etale f] [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U] (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    IsIso (etaleGlobalSectionsBaseChangeMap S F stageIso Klim P f n Ext) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
