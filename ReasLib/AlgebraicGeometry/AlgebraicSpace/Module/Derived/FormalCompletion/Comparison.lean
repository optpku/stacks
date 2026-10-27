/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.AffineBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Boundedness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition

/-! # Tensor global sections and formal-completion comparison maps -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]

/-- The coefficient map on an algebraic space over an affine base is induced by its structure morphism. -/
def limitGlobalSectionsMap {R : CommRingCat.{u}} (Y : AlgebraicSpace (Spec R)) :
    (R : Type u) →+* globalSectionsRing Y :=
  (Hom.affineGlobalSectionsMap (SchemeRealization.toBase Y)).hom

/-- Derived global sections over an affine base use the unique structure morphism. -/
def limitGlobalSections {R : CommRingCat.{u}} (Y : AlgebraicSpace (Spec R)) :
    ModuleDerived Y ⥤ DerivedCategory (ModuleCat.{u} (R : Type u)) :=
  Modules.AffineGlobalSections.functor (SchemeRealization.toBase Y)

/-- Scalar-valued derived global sections are module-valued global sections with restricted coefficients. -/
theorem limitGlobalSections_obj {R : CommRingCat.{u}}
    (Y : AlgebraicSpace (Spec R)) (E : ModuleDerived Y) :
    (limitGlobalSections Y).obj E =
      (ModuleCat.derivedRestrictionOfScalars (limitGlobalSectionsMap Y)).obj
        ((Modules.moduleDerivedGlobalSections Y).obj E) :=
  rfl

/-- The coefficient map at a finite stage is induced by its morphism to the affine stage base. -/
def stageSpaceGlobalSectionsMap
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ) :
    (A.obj (Opposite.op n) : Type u) →+* globalSectionsRing (Xn n) :=
  (Hom.affineGlobalSectionsMap (q n)).hom

/-- The finite-stage coefficient map is the canonical affine-target map. -/
theorem stageSpaceGlobalSectionsMap_eq
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ) :
    stageSpaceGlobalSectionsMap q n = (Hom.affineGlobalSectionsMap (q n)).hom :=
  rfl

/-- The two coefficient maps from the limit ring to finite-stage global functions agree. -/
theorem stageSpaceGlobalSectionsMap_comp
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (n : ℕ) :
    (stageSpaceGlobalSectionsMap q n).comp (A_lim.cone.stageMap n).hom =
      (spaceGlobalSectionsRingMap (p n)).hom.comp (limitGlobalSectionsMap X) :=
  sorry

/-- The quasi-coherent coreflection of an ambient homotopy limit, in the derived category of modules. -/
noncomputable def coherator
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) : ModuleDerived X :=
  ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj

omit [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
  [FinitePresentation (SchemeRealization.toBase X)] in
/-- `coherator Klim` is the underlying derived module of the right adjoint of
`DerivedQCoh.inclusion X` applied to `Klim`. -/
theorem coherator_obj
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) :
    coherator Klim = ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj :=
  rfl

/-- Derived global sections `M = RΓ(X, K ⊗ᴸ E)` over the limit ring, where `K` is the
quasi-coherent coreflection of the ambient homotopy limit `Klim`. -/
noncomputable def globalSectionsTensor
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) (E : ModuleDerived X) :
    DerivedCategory (ModuleCat.{u} (A_lim.cone.pt : Type u)) :=
  (limitGlobalSections X).obj
    ((DerivedTensor.Right.functor E).obj (coherator Klim))

omit [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
  [FinitePresentation (SchemeRealization.toBase X)] in
/-- `globalSectionsTensor` is derived global sections of the derived tensor of the
coherator of `Klim` with `E`. -/
theorem globalSectionsTensor_obj
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) (E : ModuleDerived X) :
    globalSectionsTensor Klim E =
      (limitGlobalSections X).obj
        ((DerivedTensor.Right.functor E).obj
          ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj) :=
  rfl

/-- The canonical map from the coherator of a presented homotopy limit to the derived
pushforward of a stage complex. -/
noncomputable def coheratorToStagePushforward
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim) (n : ℕ) :
    coherator Klim ⟶ (Modules.moduleDerivedPushforward (p n)).obj (S.K n) :=
  (Adjunction.ofIsLeftAdjoint (DerivedQCoh.inclusion X)).counit.app Klim ≫
    P.stageProjection n ≫ (stageIso n).hom

/-- `coheratorToStagePushforward` is the coherator counit, followed by the presented
stage projection and the stage identification with `R(p n)_* (S.K n)`. -/
theorem coheratorToStagePushforward_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim) (n : ℕ) :
    coheratorToStagePushforward S Ksys stageIso Klim P n =
      (Adjunction.ofIsLeftAdjoint (DerivedQCoh.inclusion X)).counit.app Klim ≫
        P.stageProjection n ≫ (stageIso n).hom :=
  rfl

/-- The geometric comparison `K ⊗ᴸ E ⟶ R(p n)_* (K_n ⊗ᴸ L(p n)^* E)` obtained by
tensoring the presented stage map and applying the projection-formula mate. -/
noncomputable def tensorToStagePushforward
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ) :
    (DerivedTensor.Right.functor E).obj (coherator Klim) ⟶
      (Modules.moduleDerivedPushforward (p n)).obj
        ((DerivedTensor.Right.functor ((modulePullbackDerived (p n)).obj E)).obj (S.K n)) :=
  (DerivedTensor.Right.functor E).map
      (coheratorToStagePushforward S Ksys stageIso Klim P n) ≫
    leftMate (p n) (S.K n) E

/-- `tensorToStagePushforward` is the derived tensor of `coheratorToStagePushforward`
followed by the projection-formula mate `leftMate`. -/
theorem tensorToStagePushforward_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ) :
    tensorToStagePushforward S Ksys stageIso Klim P E n =
      (DerivedTensor.Right.functor E).map
          (coheratorToStagePushforward S Ksys stageIso Klim P n) ≫
        leftMate (p n) (S.K n) E :=
  rfl

/-- Derived global sections of `R(p n)_* (K_n ⊗ᴸ L(p n)^* E)` over the limit ring. -/
noncomputable def globalSectionsTensorStagePushforward
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (E : ModuleDerived X) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A_lim.cone.pt : Type u)) :=
  (limitGlobalSections X).obj
    ((Modules.moduleDerivedPushforward (p n)).obj
      ((DerivedTensor.Right.functor ((modulePullbackDerived (p n)).obj E)).obj (S.K n)))

/-- The restriction-side comparison in `D(A)` induced by `tensorToStagePushforward`. -/
noncomputable def globalSectionsTensorRestrictionMap
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
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
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ) :
    globalSectionsTensorRestrictionMap S Ksys stageIso Klim P E n =
      (limitGlobalSections X).map
        (tensorToStagePushforward S Ksys stageIso Klim P E n) :=
  rfl

/-- `globalSectionsTensorStagePushforward` is derived global sections of the derived
pushforward of `K_n ⊗ᴸ L(p n)^* E`. -/
theorem globalSectionsTensorStagePushforward_obj
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (E : ModuleDerived X) (n : ℕ) :
    globalSectionsTensorStagePushforward S E n =
      (limitGlobalSections X).obj
        ((Modules.moduleDerivedPushforward (p n)).obj
          ((DerivedTensor.Right.functor ((modulePullbackDerived (p n)).obj E)).obj (S.K n))) :=
  rfl

/-- The canonical comparison `M ⊗ᴸ_A A_n ⟶ RΓ(X_n, K_n ⊗ᴸ L(p n)^* E)` in `D(A_n)`,
obtained by transposing the restriction-side composite of
the geometric restriction map with the affine direct-image isomorphism. -/
noncomputable def globalSectionsTensorBaseChangeMap
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    Ext.obj (globalSectionsTensor Klim E) ⟶
      (Modules.AffineGlobalSections.functor (q n)).obj
        ((DerivedTensor.Right.functor ((modulePullbackDerived (p n)).obj E)).obj (S.K n)) :=
  Ext.transpose
    (globalSectionsTensorRestrictionMap S Ksys stageIso Klim P E n ≫
      (Modules.AffineGlobalSections.pushforwardIso
          (φ := A_lim.cone.stageMap n)
          (f := SchemeRealization.toBase X) (f' := q n)
          (w := Category.comp_id _)
          (CommSq.mk ((SchemeRealization.eq_toBase _).trans
            (SchemeRealization.eq_toBase _).symm))).hom.app
        ((DerivedTensor.Right.functor ((modulePullbackDerived (p n)).obj E)).obj (S.K n)))

/-- `globalSectionsTensorBaseChangeMap` is the derived-extension transpose of the
restriction-side Leray composite of `globalSectionsTensorRestrictionMap`. -/
theorem globalSectionsTensorBaseChangeMap_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X)
    (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    globalSectionsTensorBaseChangeMap S Ksys stageIso Klim P E n Ext =
      Ext.transpose
        (globalSectionsTensorRestrictionMap S Ksys stageIso Klim P E n ≫
          (Modules.AffineGlobalSections.pushforwardIso
          (φ := A_lim.cone.stageMap n)
          (f := SchemeRealization.toBase X) (f' := q n)
          (w := Category.comp_id _)
          (CommSq.mk ((SchemeRealization.eq_toBase _).trans
            (SchemeRealization.eq_toBase _).symm))).hom.app
            ((DerivedTensor.Right.functor ((modulePullbackDerived (p n)).obj E)).obj
              (S.K n))) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
