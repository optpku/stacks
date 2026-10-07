module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
public import stacks_project.Chap77.Lemma_77_12_3_Comparison

/-!
# Base-change comparisons for derived tensor and internal Hom

Canonical scalar-extension maps compare derived global sections of the homotopy-limit
coherator against the finite-stage complexes, after derived tensor or internal Hom.
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

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- Projection-formula mate from `Rf_* ℱ n ⊗ᴸ E` to `Rf_*(ℱ n ⊗ᴸ Lf^* E)`. -/
def stageProjectionMate (S : ProperFlatFormalSystem) (n : ℕ) (E : ModuleDerived S.space) :
    (tensorRightFunctor E).obj
        ((Modules.pushforwardDerived (S.stageToSpace n)).obj (stageSingle S n)) ⟶
      (Modules.pushforwardDerived (S.stageToSpace n)).obj
        ((tensorRightFunctor
            ((modulePullbackDerived (S.stageToSpace n)).obj E)).obj
          (stageSingle S n)) :=
  leftMate (S.stageToSpace n) (stageSingle S n) E

/-- `stageProjectionMate` is the projection-formula left mate at a finite stage. -/
theorem stageProjectionMate_eq (S : ProperFlatFormalSystem) (n : ℕ)
    (E : ModuleDerived S.space) :
    stageProjectionMate S n E = leftMate (S.stageToSpace n) (stageSingle S n) E :=
  sorry

/-- The finite-stage derived tensor `ℱ n ⊗ᴸ E|_{X_n}`. -/
def stageTensor (S : ProperFlatFormalSystem) (n : ℕ) (E : ModuleDerived S.space) :
    ModuleDerived (S.stageSpace n) :=
  (tensorRightFunctor ((modulePullbackDerived (S.stageToSpace n)).obj E)).obj
    (stageSingle S n)

/-- `stageTensor` is fixed-right derived tensor of the stage single complex against the
derived pullback of `E`. -/
theorem stageTensor_eq (S : ProperFlatFormalSystem) (n : ℕ) (E : ModuleDerived S.space) :
    stageTensor S n E =
      (tensorRightFunctor ((modulePullbackDerived (S.stageToSpace n)).obj E)).obj
        (stageSingle S n) :=
  sorry

/-- The projection-formula comparison from the tensor of the limit-to-stage pushforward
against `E` to derived pushforward of the stage tensor. -/
def tensorLimitToStagePushforward (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (n : ℕ) :
    (tensorRightFunctor E).obj (homotopyLimitCoherator S F Klim) ⟶
      (Modules.pushforwardDerived (S.stageToSpace n)).obj (stageTensor S n E) :=
  (tensorRightFunctor E).map (limitToStagePushforward S F stageIso Klim P n) ≫
    stageProjectionMate S n E

/-- `tensorLimitToStagePushforward` is the derived tensor of `limitToStagePushforward`
followed by the projection-formula mate. -/
theorem tensorLimitToStagePushforward_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (n : ℕ) :
    tensorLimitToStagePushforward S F stageIso Klim P E n =
      (tensorRightFunctor E).map
          (limitToStagePushforward S F stageIso Klim P n) ≫
        stageProjectionMate S n E :=
  sorry

/-- Canonical Leray comparison from `RΓ(X, Rf_* G)` in `D(A)` to the restriction of
`RΓ(X_n, G)` along `A → A_n`. -/
def stagePushforwardGlobalSectionsLeray (S : ProperFlatFormalSystem) (n : ℕ)
    (G : ModuleDerived (S.stageSpace n)) :
    (globalSectionsOverLimit S).obj
        ((Modules.pushforwardDerived (S.stageToSpace n)).obj G) ⟶
      (ModuleCat.derivedRestrictionOfScalars.{u} (S.limitCone.cone.stageMap n).hom).obj
        ((globalSectionsOverStage S n).obj G) :=
  (ModuleCat.derivedRestrictionOfScalars.{u} (limitRingToGlobalSections S)).map
      (globalSectionsMapOfPushforward (S.stageToSpace n)
        (𝟙 ((Modules.pushforwardDerived (S.stageToSpace n)).obj G))) ≫
    (ModuleCat.DerivedRestriction.compObjIso (limitRingToGlobalSections S)
        (globalSectionsRingMap (S.stageToSpace n)).hom
        ((moduleDerivedGlobalSections (S.stageSpace n)).obj G)).inv ≫
    (ModuleCat.DerivedRestriction.compObjIsoOfEq
        (S.limitCone.cone.stageMap n).hom (stageRingToGlobalSections S n)
        ((globalSectionsRingMap (S.stageToSpace n)).hom.comp
          (limitRingToGlobalSections S))
        (stageRingToGlobalSections_comp S n).symm
        ((moduleDerivedGlobalSections (S.stageSpace n)).obj G)).hom

/-- `stagePushforwardGlobalSectionsLeray` is restriction of the underived-space Leray map,
reassociated along `A → Γ(X) → Γ(X_n)` and `A → A_n → Γ(X_n)`. -/
theorem stagePushforwardGlobalSectionsLeray_eq (S : ProperFlatFormalSystem) (n : ℕ)
    (G : ModuleDerived (S.stageSpace n)) :
    stagePushforwardGlobalSectionsLeray S n G =
      (ModuleCat.derivedRestrictionOfScalars.{u} (limitRingToGlobalSections S)).map
          (globalSectionsMapOfPushforward (S.stageToSpace n)
            (𝟙 ((Modules.pushforwardDerived (S.stageToSpace n)).obj G))) ≫
        (ModuleCat.DerivedRestriction.compObjIso (limitRingToGlobalSections S)
            (globalSectionsRingMap (S.stageToSpace n)).hom
            ((moduleDerivedGlobalSections (S.stageSpace n)).obj G)).inv ≫
        (ModuleCat.DerivedRestriction.compObjIsoOfEq
            (S.limitCone.cone.stageMap n).hom (stageRingToGlobalSections S n)
            ((globalSectionsRingMap (S.stageToSpace n)).hom.comp
              (limitRingToGlobalSections S))
            (stageRingToGlobalSections_comp S n).symm
            ((moduleDerivedGlobalSections (S.stageSpace n)).obj G)).hom :=
  sorry

/-- The restriction-side comparison in `D(A)` induced by `tensorLimitToStagePushforward`. -/
def globalSectionsTensorRestrictionMap (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (n : ℕ) :
    (globalSectionsOverLimit S).obj
        ((tensorRightFunctor E).obj (homotopyLimitCoherator S F Klim)) ⟶
      (globalSectionsOverLimit S).obj
        ((Modules.pushforwardDerived (S.stageToSpace n)).obj (stageTensor S n E)) :=
  (globalSectionsOverLimit S).map (tensorLimitToStagePushforward S F stageIso Klim P E n)

/-- `globalSectionsTensorRestrictionMap` is derived global sections of
`tensorLimitToStagePushforward`. -/
theorem globalSectionsTensorRestrictionMap_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (n : ℕ) :
    globalSectionsTensorRestrictionMap S F stageIso Klim P E n =
      (globalSectionsOverLimit S).map
        (tensorLimitToStagePushforward S F stageIso Klim P E n) :=
  sorry

/-- The canonical comparison `M ⊗ᴸ_A A_n ⟶ RΓ(X_n, ℱ n ⊗ᴸ E|_{X_n})` in `D(A_n)`. -/
def globalSectionsTensorBaseChangeMap (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    Ext.obj
        ((globalSectionsOverLimit S).obj
          ((tensorRightFunctor E).obj (homotopyLimitCoherator S F Klim))) ⟶
      (globalSectionsOverStage S n).obj (stageTensor S n E) :=
  Ext.transpose
    (globalSectionsTensorRestrictionMap S F stageIso Klim P E n ≫
      stagePushforwardGlobalSectionsLeray S n (stageTensor S n E))

/-- `globalSectionsTensorBaseChangeMap` is the derived-extension transpose of the
restriction-side Leray composite of `globalSectionsTensorRestrictionMap`. -/
theorem globalSectionsTensorBaseChangeMap_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    globalSectionsTensorBaseChangeMap S F stageIso Klim P E n Ext =
      Ext.transpose
        (globalSectionsTensorRestrictionMap S F stageIso Klim P E n ≫
          stagePushforwardGlobalSectionsLeray S n (stageTensor S n E)) :=
  sorry

/-- Finite-stage derived internal Hom from `E|_{X_n}` into `ℱ n`. -/
def stageInternalHom (S : ProperFlatFormalSystem) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) :
    ModuleDerived (S.stageSpace n) :=
  (ihomOf H_n ((modulePullbackDerived (S.stageToSpace n)).obj E)).obj (stageSingle S n)

/-- `stageInternalHom` is internal Hom of the derived pullback of `E` into the stage
single complex. -/
theorem stageInternalHom_eq (S : ProperFlatFormalSystem) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) :
    stageInternalHom S n H_n E =
      (ihomOf H_n ((modulePullbackDerived (S.stageToSpace n)).obj E)).obj
        (stageSingle S n) :=
  sorry

/-- The internal-Hom comparison from the limit-to-stage pushforward, after transposing
across `Lf^* ⊣ Rf_*` and the pullback/internal-Hom comparison. -/
def homLimitToStagePushforward (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    [BraidedCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (H : MonoidalClosed (ModuleDerived S.space)) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    [BraidedCategory (ModuleDerived (S.stageSpace n))]
    [(modulePullbackDerived (S.stageToSpace n)).Monoidal]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) :
    (ihomOf H E).obj (homotopyLimitCoherator S F Klim) ⟶
      (Modules.pushforwardDerived (S.stageToSpace n)).obj (stageInternalHom S n H_n E) :=
  (ihomOf H E).map (limitToStagePushforward S F stageIso Klim P n) ≫
    (modulePullbackDerivedPushforwardAdjunction (S.stageToSpace n)).homEquiv _ _
      (Functor.PullbackInternalHom.comparisonOf H H_n
          (modulePullbackDerived (S.stageToSpace n))
          (fun A B ↦ (Functor.Monoidal.μIso
              (modulePullbackDerived (S.stageToSpace n)) A B).symm)
          E ((Modules.pushforwardDerived (S.stageToSpace n)).obj (stageSingle S n)) ≫
        (ihomOf H_n ((modulePullbackDerived (S.stageToSpace n)).obj E)).map
          ((modulePullbackDerivedPushforwardAdjunction (S.stageToSpace n)).counit.app
            (stageSingle S n)))

/-- `homLimitToStagePushforward` is internal Hom of the limit-to-stage map, followed by the
adjunct of the pullback/internal-Hom comparison against the counit. -/
theorem homLimitToStagePushforward_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    [BraidedCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (H : MonoidalClosed (ModuleDerived S.space)) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    [BraidedCategory (ModuleDerived (S.stageSpace n))]
    [(modulePullbackDerived (S.stageToSpace n)).Monoidal]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) :
    homLimitToStagePushforward S F stageIso Klim P H n H_n E =
      (ihomOf H E).map (limitToStagePushforward S F stageIso Klim P n) ≫
        (modulePullbackDerivedPushforwardAdjunction (S.stageToSpace n)).homEquiv _ _
          (Functor.PullbackInternalHom.comparisonOf H H_n
              (modulePullbackDerived (S.stageToSpace n))
              (fun A B ↦ (Functor.Monoidal.μIso
                  (modulePullbackDerived (S.stageToSpace n)) A B).symm)
              E ((Modules.pushforwardDerived (S.stageToSpace n)).obj (stageSingle S n)) ≫
            (ihomOf H_n ((modulePullbackDerived (S.stageToSpace n)).obj E)).map
              ((modulePullbackDerivedPushforwardAdjunction (S.stageToSpace n)).counit.app
                (stageSingle S n))) :=
  sorry

/-- The restriction-side comparison in `D(A)` induced by `homLimitToStagePushforward`. -/
def globalHomRestrictionMap (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    [BraidedCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (H : MonoidalClosed (ModuleDerived S.space)) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    [BraidedCategory (ModuleDerived (S.stageSpace n))]
    [(modulePullbackDerived (S.stageToSpace n)).Monoidal]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) :
    (globalSectionsOverLimit S).obj ((ihomOf H E).obj (homotopyLimitCoherator S F Klim)) ⟶
      (globalSectionsOverLimit S).obj
        ((Modules.pushforwardDerived (S.stageToSpace n)).obj
          (stageInternalHom S n H_n E)) :=
  (globalSectionsOverLimit S).map
    (homLimitToStagePushforward S F stageIso Klim P H n H_n E)

/-- `globalHomRestrictionMap` is derived global sections of `homLimitToStagePushforward`. -/
theorem globalHomRestrictionMap_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    [BraidedCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (H : MonoidalClosed (ModuleDerived S.space)) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    [BraidedCategory (ModuleDerived (S.stageSpace n))]
    [(modulePullbackDerived (S.stageToSpace n)).Monoidal]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space) :
    globalHomRestrictionMap S F stageIso Klim P H n H_n E =
      (globalSectionsOverLimit S).map
        (homLimitToStagePushforward S F stageIso Klim P H n H_n E) :=
  sorry

/-- The canonical comparison `N ⊗ᴸ_A A_n ⟶ RHom_{X_n}(E|_{X_n}, ℱ n)` in `D(A_n)`. -/
def globalHomBaseChangeMap (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    [BraidedCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (H : MonoidalClosed (ModuleDerived S.space)) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    [BraidedCategory (ModuleDerived (S.stageSpace n))]
    [(modulePullbackDerived (S.stageToSpace n)).Monoidal]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    Ext.obj
        ((globalSectionsOverLimit S).obj
          ((ihomOf H E).obj (homotopyLimitCoherator S F Klim))) ⟶
      (globalSectionsOverStage S n).obj (stageInternalHom S n H_n E) :=
  Ext.transpose
    (globalHomRestrictionMap S F stageIso Klim P H n H_n E ≫
      stagePushforwardGlobalSectionsLeray S n (stageInternalHom S n H_n E))

/-- `globalHomBaseChangeMap` is the derived-extension transpose of the restriction-side
Leray composite of `globalHomRestrictionMap`. -/
theorem globalHomBaseChangeMap_eq (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    [MonoidalCategory (ModuleDerived S.space)]
    [BraidedCategory (ModuleDerived S.space)]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (H : MonoidalClosed (ModuleDerived S.space)) (n : ℕ)
    [MonoidalCategory (ModuleDerived (S.stageSpace n))]
    [BraidedCategory (ModuleDerived (S.stageSpace n))]
    [(modulePullbackDerived (S.stageToSpace n)).Monoidal]
    (H_n : MonoidalClosed (ModuleDerived (S.stageSpace n)))
    (E : ModuleDerived S.space)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    globalHomBaseChangeMap S F stageIso Klim P H n H_n E Ext =
      Ext.transpose
        (globalHomRestrictionMap S F stageIso Klim P H n H_n E ≫
          stagePushforwardGlobalSectionsLeray S n (stageInternalHom S n H_n E)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
