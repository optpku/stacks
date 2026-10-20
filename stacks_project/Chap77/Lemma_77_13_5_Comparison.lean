/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap77.Lemma_77_13_3_Comparison

/-!
# Derived global sections of an étale open after formal-completion base change

In Situation 77.13.1, with `K` the quasi-coherent coreflection of a homotopy
limit of the pushforwards of the stages `K n`, this module owns `RΓ(U, K)` for
a morphism `U ⟶ X` and the canonical comparison with `RΓ(U_n, K_n)` in `D(A_n)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable (p : ∀ n, Xn n ⟶ X)
variable (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n)
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]
variable {U : AlgebraicSpace (Spec A_lim.cone.pt)}

/-- The finite-stage fibre product `U_n = U ×_X X_n`. -/
noncomputable def stagePullback (f : U ⟶ X) (n : ℕ) :
    AlgebraicSpace (Spec A_lim.cone.pt) :=
  Limits.pullback f (p n)

/-- `stagePullback p f n` is the categorical fibre product of `f` and `p n`. -/
theorem stagePullback_eq (f : U ⟶ X) (n : ℕ) :
    stagePullback p f n = Limits.pullback f (p n) :=
  sorry

/-- The projection `U_n ⟶ U` of the finite-stage fibre product. -/
noncomputable abbrev stagePullback_fst (f : U ⟶ X) (n : ℕ) :
    stagePullback p f n ⟶ U :=
  Limits.pullback.fst f (p n)

/-- `stagePullback_fst` is the first projection of `U ×_X X_n`. -/
theorem stagePullback_fst_eq (f : U ⟶ X) (n : ℕ) :
    stagePullback_fst p f n = Limits.pullback.fst f (p n) :=
  sorry

/-- The projection `U_n ⟶ X_n` of the finite-stage fibre product. -/
noncomputable abbrev stagePullback_snd (f : U ⟶ X) (n : ℕ) :
    stagePullback p f n ⟶ Xn n :=
  Limits.pullback.snd f (p n)

/-- `stagePullback_snd` is the second projection of `U ×_X X_n`. -/
theorem stagePullback_snd_eq (f : U ⟶ X) (n : ℕ) :
    stagePullback_snd p f n = Limits.pullback.snd f (p n) :=
  sorry

/-- The projections exhibit `U_n` as the fibre product `U ×_X X_n`. -/
theorem stagePullback_isPullback (f : U ⟶ X) (n : ℕ) :
    IsPullback (stagePullback_fst p f n) (stagePullback_snd p f n) f (p n) :=
  sorry

/-- Derived global sections `RΓ(U, K)` over the limit ring, where `K` is the
quasi-coherent coreflection of the ambient homotopy limit `Klim` and the
restriction to `U` is derived pullback along `f`. -/
noncomputable def etaleGlobalSections
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) (f : U ⟶ X) :
    DerivedCategory (ModuleCat.{u} (A_lim.cone.pt : Type u)) :=
  (limitGlobalSections U).obj ((modulePullbackDerived f).obj (coherator Klim))

/-- `etaleGlobalSections` is derived global sections of the derived pullback of
the coherator of `Klim` along `f`. -/
theorem etaleGlobalSections_obj
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) (f : U ⟶ X) :
    etaleGlobalSections Klim f =
      (limitGlobalSections U).obj
        ((modulePullbackDerived f).obj (coherator Klim)) :=
  sorry

/-- The ring map `A_n →+* Γ(U_n, 𝒪)` obtained by composing `A_n → Γ(X_n)` with
the map on global sections induced by `U_n ⟶ X_n`. -/
noncomputable def etaleStageSpaceGlobalSectionsMap (f : U ⟶ X) (n : ℕ) :
    (A.obj (Opposite.op n) : Type u) →+* globalSectionsRing (stagePullback p f n) :=
  (spaceGlobalSectionsRingMap (stagePullback_snd p f n)).hom.comp
    (stageSpaceGlobalSectionsMap q n)

/-- `etaleStageSpaceGlobalSectionsMap` is the composite of
`stageSpaceGlobalSectionsMap` with the map on global sections induced by the
projection `U_n ⟶ X_n`. -/
theorem etaleStageSpaceGlobalSectionsMap_eq (f : U ⟶ X) (n : ℕ) :
    etaleStageSpaceGlobalSectionsMap p q f n =
      (spaceGlobalSectionsRingMap (stagePullback_snd p f n)).hom.comp
        (stageSpaceGlobalSectionsMap q n) :=
  sorry

/-- The two paths `A → A_n → Γ(U_n)` and `A → Γ(U) → Γ(U_n)` agree. -/
theorem etaleStageSpaceGlobalSectionsMap_comp (f : U ⟶ X) (n : ℕ) :
    (etaleStageSpaceGlobalSectionsMap p q f n).comp (A_lim.cone.stageMap n).hom =
      (spaceGlobalSectionsRingMap (stagePullback_fst p f n)).hom.comp
        (limitGlobalSectionsMap U) :=
  sorry

/-- Derived global sections of a finite-stage fibre product, as a functor to
`D(A_n)`. -/
noncomputable def etaleStageGlobalSections (f : U ⟶ X) (n : ℕ) :
    ModuleDerived (stagePullback p f n) ⥤
      DerivedCategory (ModuleCat.{u} (A.obj (Opposite.op n) : Type u)) :=
  Modules.moduleDerivedGlobalSections (stagePullback p f n) ⋙
    ModuleCat.derivedRestrictionOfScalars (etaleStageSpaceGlobalSectionsMap p q f n)

/-- On objects, `etaleStageGlobalSections p q f n` is `RΓ(U_n, E)`, viewed in
`D(A_n)`. -/
theorem etaleStageGlobalSections_obj (f : U ⟶ X) (n : ℕ)
    (E : ModuleDerived (stagePullback p f n)) :
    (etaleStageGlobalSections p q f n).obj E =
      (ModuleCat.derivedRestrictionOfScalars
          (etaleStageSpaceGlobalSectionsMap p q f n)).obj
        ((Modules.moduleDerivedGlobalSections (stagePullback p f n)).obj E) :=
  sorry

/-- The geometric comparison `L f^* K ⟶ R(fst)_* L(snd)^* (K n)` obtained by
derived-pulling back the presented stage map and applying the cartesian
derived base-change mate on `U_n = U ×_X X_n`. -/
noncomputable def etaleCoheratorToStage
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.fst f (p n)) f)]
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.snd f (p n)) (p n))] :
    (modulePullbackDerived f).obj (coherator Klim) ⟶
      (Modules.pushforwardDerived (stagePullback_fst p f n)).obj
        ((modulePullbackDerived (stagePullback_snd p f n)).obj (S.K n)) :=
  (modulePullbackDerived f).map
      (coheratorToStagePushforward S Ksys stageIso Klim P n) ≫
    Hom.DerivedBaseChange.app
      (IsPullback.of_hasPullback f (p n)).flip.toCommSq (S.K n)

/-- `etaleCoheratorToStage` is derived pullback of `coheratorToStagePushforward`
followed by the cartesian derived base-change component at `S.K n`. -/
theorem etaleCoheratorToStage_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.fst f (p n)) f)]
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.snd f (p n)) (p n))] :
    etaleCoheratorToStage p q S Ksys stageIso Klim P f n =
      (modulePullbackDerived f).map
          (coheratorToStagePushforward S Ksys stageIso Klim P n) ≫
        Hom.DerivedBaseChange.app
          (IsPullback.of_hasPullback f (p n)).flip.toCommSq (S.K n) :=
  sorry

/-- Canonical Leray comparison from `RΓ(U, R(fst)_* G)` in `D(A)` to the
restriction of `RΓ(U_n, G)` along `A → A_n`. -/
noncomputable def etalePushforwardGlobalSectionsLeray
    (f : U ⟶ X) (n : ℕ) (G : ModuleDerived (stagePullback p f n)) :
    (limitGlobalSections U).obj
        ((Modules.pushforwardDerived (stagePullback_fst p f n)).obj G) ⟶
      (ModuleCat.derivedRestrictionOfScalars (A_lim.cone.stageMap n).hom).obj
        ((etaleStageGlobalSections p q f n).obj G) :=
  (ModuleCat.derivedRestrictionOfScalars (limitGlobalSectionsMap U)).map
      (spaceGlobalSectionsMapOfPushforward (stagePullback_fst p f n)
        (𝟙 ((Modules.pushforwardDerived (stagePullback_fst p f n)).obj G))) ≫
    (ModuleCat.DerivedRestriction.compObjIso (limitGlobalSectionsMap U)
        (spaceGlobalSectionsRingMap (stagePullback_fst p f n)).hom
        ((Modules.moduleDerivedGlobalSections (stagePullback p f n)).obj G)).inv ≫
    (ModuleCat.DerivedRestriction.compObjIsoOfEq (A_lim.cone.stageMap n).hom
        (etaleStageSpaceGlobalSectionsMap p q f n)
        ((spaceGlobalSectionsRingMap (stagePullback_fst p f n)).hom.comp
          (limitGlobalSectionsMap U))
        (etaleStageSpaceGlobalSectionsMap_comp p q f n).symm
        ((Modules.moduleDerivedGlobalSections (stagePullback p f n)).obj G)).hom

/-- `etalePushforwardGlobalSectionsLeray` is restriction of the underived-space
Leray map, reassociated along `A → Γ(U) → Γ(U_n)` and `A → A_n → Γ(U_n)`. -/
theorem etalePushforwardGlobalSectionsLeray_def
    (f : U ⟶ X) (n : ℕ) (G : ModuleDerived (stagePullback p f n)) :
    etalePushforwardGlobalSectionsLeray p q f n G =
      (ModuleCat.derivedRestrictionOfScalars (limitGlobalSectionsMap U)).map
          (spaceGlobalSectionsMapOfPushforward (stagePullback_fst p f n)
            (𝟙 ((Modules.pushforwardDerived (stagePullback_fst p f n)).obj G))) ≫
        (ModuleCat.DerivedRestriction.compObjIso (limitGlobalSectionsMap U)
            (spaceGlobalSectionsRingMap (stagePullback_fst p f n)).hom
            ((Modules.moduleDerivedGlobalSections (stagePullback p f n)).obj G)).inv ≫
        (ModuleCat.DerivedRestriction.compObjIsoOfEq
            (A_lim.cone.stageMap n).hom (etaleStageSpaceGlobalSectionsMap p q f n)
            ((spaceGlobalSectionsRingMap (stagePullback_fst p f n)).hom.comp
              (limitGlobalSectionsMap U))
            (etaleStageSpaceGlobalSectionsMap_comp p q f n).symm
            ((Modules.moduleDerivedGlobalSections (stagePullback p f n)).obj
              G)).hom :=
  sorry

/-- The restriction-side comparison in `D(A)` induced by `etaleCoheratorToStage`,
followed by the Leray reassociation to the restriction of `RΓ(U_n, K_n)`. -/
noncomputable def etaleGlobalSectionsRestrictionMap
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.fst f (p n)) f)]
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.snd f (p n)) (p n))] :
    etaleGlobalSections Klim f ⟶
      (ModuleCat.derivedRestrictionOfScalars (A_lim.cone.stageMap n).hom).obj
        ((etaleStageGlobalSections p q f n).obj
          ((modulePullbackDerived (stagePullback_snd p f n)).obj (S.K n))) :=
  (limitGlobalSections U).map
      (etaleCoheratorToStage p q S Ksys stageIso Klim P f n) ≫
    etalePushforwardGlobalSectionsLeray p q f n
      ((modulePullbackDerived (stagePullback_snd p f n)).obj (S.K n))

/-- `etaleGlobalSectionsRestrictionMap` is derived global sections of
`etaleCoheratorToStage`, followed by `etalePushforwardGlobalSectionsLeray`. -/
theorem etaleGlobalSectionsRestrictionMap_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.fst f (p n)) f)]
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.snd f (p n)) (p n))] :
    etaleGlobalSectionsRestrictionMap p q S Ksys stageIso Klim P f n =
      (limitGlobalSections U).map
          (etaleCoheratorToStage p q S Ksys stageIso Klim P f n) ≫
        etalePushforwardGlobalSectionsLeray p q f n
          ((modulePullbackDerived (stagePullback_snd p f n)).obj (S.K n)) :=
  sorry

/-- The canonical comparison `RΓ(U, K) ⊗ᴸ_A A_n ⟶ RΓ(U_n, K_n)` in `D(A_n)`,
obtained by transposing `etaleGlobalSectionsRestrictionMap`. -/
noncomputable def etaleGlobalSectionsBaseChangeMap
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.fst f (p n)) f)]
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.snd f (p n)) (p n))]
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    Ext.obj (etaleGlobalSections Klim f) ⟶
      (etaleStageGlobalSections p q f n).obj
        ((modulePullbackDerived (stagePullback_snd p f n)).obj (S.K n)) :=
  Ext.transpose
    (etaleGlobalSectionsRestrictionMap p q S Ksys stageIso Klim P f n)

/-- `etaleGlobalSectionsBaseChangeMap` is the derived-extension transpose of
`etaleGlobalSectionsRestrictionMap`. -/
theorem etaleGlobalSectionsBaseChangeMap_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.fst f (p n)) f)]
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.snd f (p n)) (p n))]
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    etaleGlobalSectionsBaseChangeMap p q S Ksys stageIso Klim P f n Ext =
      Ext.transpose
        (etaleGlobalSectionsRestrictionMap p q S Ksys stageIso Klim P f n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
