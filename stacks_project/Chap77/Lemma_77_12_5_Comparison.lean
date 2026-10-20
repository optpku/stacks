module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap77.Lemma_77_12_3_Comparison
public import stacks_project.Chap77.Lemma_77_12_5_Pullback

/-!
# Derived global sections of an étale open after stage base change

In Situation 77.12.1, with `K` the quasi-coherent coreflection of a homotopy limit of
the pushforwards of the stages `ℱ n`, this module owns `RΓ(U, K)` for a morphism
`U ⟶ X` and the canonical comparison with `RΓ(U_n, ℱ n)` in `D(A_n)`.
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

/-- The successor map of pushed stage sheaves, obtained by adjoining the stage
transition isomorphism, composing the iterated pushforward, and transporting along
`stageMap_comp_stageToSpace`. -/
def pushedStageSuccessor (S : ProperFlatFormalSystem) (n : ℕ) :
    S.pushforwardModule (n + 1) ⟶ S.pushforwardModule n :=
  (Modules.pushforward (S.stageToSpace (n + 1))).map
      (((Modules.pullbackPushforwardAdjunction (S.stageMap n)).homEquiv
          (S.moduleSheaf (n + 1)) (S.moduleSheaf n)) (S.moduleTransitionIso n).hom) ≫
    (Modules.pushforwardComp (S.stageMap n) (S.stageToSpace (n + 1))).hom.app
      (S.moduleSheaf n) ≫
    eqToHom (congrArg (fun g : S.stageSpace n ⟶ S.space ↦
      (Modules.pushforward g).obj (S.moduleSheaf n)) (S.stageMap_comp_stageToSpace n))

/-- `pushedStageSuccessor` is the adjoint of the stage transition, followed by the
pushforward composition isomorphism and the identification
`stageMap n ≫ stageToSpace (n + 1) = stageToSpace n`. -/
theorem pushedStageSuccessor_eq (S : ProperFlatFormalSystem) (n : ℕ) :
    pushedStageSuccessor S n =
      (Modules.pushforward (S.stageToSpace (n + 1))).map
          (((Modules.pullbackPushforwardAdjunction (S.stageMap n)).homEquiv
              (S.moduleSheaf (n + 1)) (S.moduleSheaf n)) (S.moduleTransitionIso n).hom) ≫
        (Modules.pushforwardComp (S.stageMap n) (S.stageToSpace (n + 1))).hom.app
          (S.moduleSheaf n) ≫
        eqToHom (congrArg (fun g : S.stageSpace n ⟶ S.space ↦
          (Modules.pushforward g).obj (S.moduleSheaf n)) (S.stageMap_comp_stageToSpace n)) :=
  sorry

/-- Derived global sections `RΓ(U, -)` over the inverse-limit ring, via restriction of
scalars along `A → Γ(X) → Γ(U)`. -/
def etaleGlobalSectionsOver (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) :
    ModuleDerived U ⥤ DerivedCategory (ModuleCat.{u} (limitRing S)) :=
  moduleDerivedGlobalSections U ⋙
    ModuleCat.derivedRestrictionOfScalars.{u}
      ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))

/-- On objects, `etaleGlobalSectionsOver S f` is `RΓ(U, E)` viewed in `D(A)`. -/
theorem etaleGlobalSectionsOver_obj (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space)
    (E : ModuleDerived U) :
    (etaleGlobalSectionsOver S f).obj E =
      (ModuleCat.derivedRestrictionOfScalars.{u}
          ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))).obj
        ((moduleDerivedGlobalSections U).obj E) :=
  sorry

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
  sorry

/-- The ring map `A_n →+* Γ(U_n, 𝒪)` obtained by composing `A_n → Γ(X_n)` with the map
on global sections induced by `U_n ⟶ X_n`. -/
def etaleStageRingToGlobalSections (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    stageRing S n →+* (globalSectionsRing (stagePullback S f n) : Type u) :=
  (globalSectionsRingMap (stagePullback_snd S f n)).hom.comp
    (stageRingToGlobalSections S n)

/-- `etaleStageRingToGlobalSections` is the composite of `stageRingToGlobalSections`
with the map on global sections induced by the projection `U_n ⟶ X_n`. -/
theorem etaleStageRingToGlobalSections_eq (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    etaleStageRingToGlobalSections S f n =
      (globalSectionsRingMap (stagePullback_snd S f n)).hom.comp
        (stageRingToGlobalSections S n) :=
  sorry

/-- The two paths `A → A_n → Γ(U_n)` and `A → Γ(U) → Γ(U_n)` agree. -/
theorem etaleStageRingToGlobalSections_comp (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    (etaleStageRingToGlobalSections S f n).comp (S.limitCone.cone.stageMap n).hom =
      (globalSectionsRingMap (stagePullback_fst S f n)).hom.comp
        ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S)) :=
  sorry

/-- Derived global sections of a finite-stage fibre product, as a functor to `D(A_n)`. -/
def etaleStageGlobalSections (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ) :
    ModuleDerived (stagePullback S f n) ⥤
      DerivedCategory (ModuleCat.{u} (stageRing S n)) :=
  moduleDerivedGlobalSections (stagePullback S f n) ⋙
    ModuleCat.derivedRestrictionOfScalars.{u} (etaleStageRingToGlobalSections S f n)

/-- On objects, `etaleStageGlobalSections S f n` is `RΓ(U_n, E)`, viewed in `D(A_n)`. -/
theorem etaleStageGlobalSections_obj (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    (E : ModuleDerived (stagePullback S f n)) :
    (etaleStageGlobalSections S f n).obj E =
      (ModuleCat.derivedRestrictionOfScalars.{u}
          (etaleStageRingToGlobalSections S f n)).obj
        ((moduleDerivedGlobalSections (stagePullback S f n)).obj E) :=
  sorry

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
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.fst f (S.stageToSpace n)) f)]
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.snd f (S.stageToSpace n)) (S.stageToSpace n))] :
    (modulePullbackDerived f).obj (homotopyLimitCoherator S F Klim) ⟶
      (Modules.pushforwardDerived (stagePullback_fst S f n)).obj
        ((modulePullbackDerived (stagePullback_snd S f n)).obj (stageSingle S n)) :=
  (modulePullbackDerived f).map (limitToStagePushforward S F stageIso Klim P n) ≫
    Hom.DerivedBaseChange.app
      (IsPullback.of_hasPullback f (S.stageToSpace n)).flip.toCommSq (stageSingle S n)

/-- `etaleCoheratorToStage` is derived pullback of `limitToStagePushforward` followed by
the cartesian derived base-change component at `stageSingle S n`. -/
theorem etaleCoheratorToStage_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.fst f (S.stageToSpace n)) f)]
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.snd f (S.stageToSpace n)) (S.stageToSpace n))] :
    etaleCoheratorToStage S F stageIso Klim P f n =
      (modulePullbackDerived f).map (limitToStagePushforward S F stageIso Klim P n) ≫
        Hom.DerivedBaseChange.app
          (IsPullback.of_hasPullback f (S.stageToSpace n)).flip.toCommSq
          (stageSingle S n) :=
  sorry

/-- Canonical Leray comparison from `RΓ(U, R(fst)_* G)` in `D(A)` to the restriction of
`RΓ(U_n, G)` along `A → A_n`. -/
def etalePushforwardGlobalSectionsLeray (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    (G : ModuleDerived (stagePullback S f n)) :
    (etaleGlobalSectionsOver S f).obj
        ((Modules.pushforwardDerived (stagePullback_fst S f n)).obj G) ⟶
      (ModuleCat.derivedRestrictionOfScalars.{u}
          (S.limitCone.cone.stageMap n).hom).obj
        ((etaleStageGlobalSections S f n).obj G) :=
  (ModuleCat.derivedRestrictionOfScalars.{u}
        ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))).map
      (globalSectionsMapOfPushforward (stagePullback_fst S f n)
        (𝟙 ((Modules.pushforwardDerived (stagePullback_fst S f n)).obj G))) ≫
    (ModuleCat.DerivedRestriction.compObjIso
        ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))
        (globalSectionsRingMap (stagePullback_fst S f n)).hom
        ((moduleDerivedGlobalSections (stagePullback S f n)).obj G)).inv ≫
    (ModuleCat.DerivedRestriction.compObjIsoOfEq
        (S.limitCone.cone.stageMap n).hom (etaleStageRingToGlobalSections S f n)
        ((globalSectionsRingMap (stagePullback_fst S f n)).hom.comp
          ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S)))
        (etaleStageRingToGlobalSections_comp S f n).symm
        ((moduleDerivedGlobalSections (stagePullback S f n)).obj G)).hom

/-- `etalePushforwardGlobalSectionsLeray` is restriction of the underived-space Leray
map, reassociated along `A → Γ(U) → Γ(U_n)` and `A → A_n → Γ(U_n)`. -/
theorem etalePushforwardGlobalSectionsLeray_eq (S : ProperFlatFormalSystem)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    (G : ModuleDerived (stagePullback S f n)) :
    etalePushforwardGlobalSectionsLeray S f n G =
      (ModuleCat.derivedRestrictionOfScalars.{u}
            ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))).map
          (globalSectionsMapOfPushforward (stagePullback_fst S f n)
            (𝟙 ((Modules.pushforwardDerived (stagePullback_fst S f n)).obj G))) ≫
        (ModuleCat.DerivedRestriction.compObjIso
            ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S))
            (globalSectionsRingMap (stagePullback_fst S f n)).hom
            ((moduleDerivedGlobalSections (stagePullback S f n)).obj G)).inv ≫
        (ModuleCat.DerivedRestriction.compObjIsoOfEq
            (S.limitCone.cone.stageMap n).hom (etaleStageRingToGlobalSections S f n)
            ((globalSectionsRingMap (stagePullback_fst S f n)).hom.comp
              ((globalSectionsRingMap f).hom.comp (limitRingToGlobalSections S)))
            (etaleStageRingToGlobalSections_comp S f n).symm
            ((moduleDerivedGlobalSections (stagePullback S f n)).obj G)).hom :=
  sorry

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
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.fst f (S.stageToSpace n)) f)]
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.snd f (S.stageToSpace n)) (S.stageToSpace n))] :
    etaleGlobalSections S F Klim f ⟶
      (ModuleCat.derivedRestrictionOfScalars.{u}
          (S.limitCone.cone.stageMap n).hom).obj
        ((etaleStageGlobalSections S f n).obj
          ((modulePullbackDerived (stagePullback_snd S f n)).obj (stageSingle S n))) :=
  (etaleGlobalSectionsOver S f).map (etaleCoheratorToStage S F stageIso Klim P f n) ≫
    etalePushforwardGlobalSectionsLeray S f n
      ((modulePullbackDerived (stagePullback_snd S f n)).obj (stageSingle S n))

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
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.fst f (S.stageToSpace n)) f)]
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.snd f (S.stageToSpace n)) (S.stageToSpace n))] :
    etaleGlobalSectionsRestrictionMap S F stageIso Klim P f n =
      (etaleGlobalSectionsOver S f).map
          (etaleCoheratorToStage S F stageIso Klim P f n) ≫
        etalePushforwardGlobalSectionsLeray S f n
          ((modulePullbackDerived (stagePullback_snd S f n)).obj (stageSingle S n)) :=
  sorry

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
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.fst f (S.stageToSpace n)) f)]
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.snd f (S.stageToSpace n)) (S.stageToSpace n))]
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    Ext.obj (etaleGlobalSections S F Klim f) ⟶
      (etaleStageGlobalSections S f n).obj
        ((modulePullbackDerived (stagePullback_snd S f n)).obj (stageSingle S n)) :=
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
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.fst f (S.stageToSpace n)) f)]
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.snd f (S.stageToSpace n)) (S.stageToSpace n))]
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    etaleGlobalSectionsBaseChangeMap S F stageIso Klim P f n Ext =
      Ext.transpose (etaleGlobalSectionsRestrictionMap S F stageIso Klim P f n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
