/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange

/-! # Étale global sections and formal-completion base change -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
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
variable [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
  [FinitePresentation (SchemeRealization.toBase X)]
variable {U : AlgebraicSpace (Spec A_lim.cone.pt)}

/-- Derived global sections `RΓ(U, K)` over the limit ring, where `K` is the
quasi-coherent coreflection of the ambient homotopy limit `Klim` and the
restriction to `U` is derived pullback along `f`. -/
noncomputable def etaleGlobalSections
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) (f : U ⟶ X) :
    DerivedCategory (ModuleCat.{u} (A_lim.cone.pt : Type u)) :=
  (limitGlobalSections U).obj ((modulePullbackDerived f).obj (coherator Klim))

omit [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
  [FinitePresentation (SchemeRealization.toBase X)] in
/-- `etaleGlobalSections` is derived global sections of the derived pullback of
the coherator of `Klim` along `f`. -/
theorem etaleGlobalSections_obj
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Klim : ModuleDerived X) (f : U ⟶ X) :
    etaleGlobalSections Klim f =
      (limitGlobalSections U).obj
        ((modulePullbackDerived f).obj (coherator Klim)) :=
  rfl

/-- Derived global sections on the finite-stage fibre product, with coefficients
induced by its projection to the affine stage base. -/
noncomputable def etaleStageGlobalSections (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (f : U ⟶ X) (n : ℕ) :
    ModuleDerived (Limits.pullback f (p n)) ⥤
      DerivedCategory (ModuleCat.{u} (A.obj (Opposite.op n) : Type u)) :=
  Modules.AffineGlobalSections.functor (Limits.pullback.snd f (p n) ≫ q n)

/-- Stage global sections are computed using the affine coefficient structure
of the second projection followed by the stage structure morphism. -/
theorem etaleStageGlobalSections_obj (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (f : U ⟶ X) (n : ℕ)
    (E : ModuleDerived (Limits.pullback f (p n))) :
    (etaleStageGlobalSections p q f n).obj E =
      (Modules.AffineGlobalSections.functor
        (Limits.pullback.snd f (p n) ≫ q n)).obj E :=
  rfl

/-- The geometric comparison `L f^* K ⟶ R(fst)_* L(snd)^* (K n)` obtained by
derived-pulling back the presented stage map and applying the cartesian
derived base-change mate on `U_n = U ×_X X_n`. -/
noncomputable def etaleCoheratorToStage
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ) :
    (modulePullbackDerived f).obj (coherator Klim) ⟶
      (Modules.moduleDerivedPushforward (Limits.pullback.fst f (p n))).obj
        ((modulePullbackDerived (Limits.pullback.snd f (p n))).obj (S.K n)) :=
  (modulePullbackDerived f).map
      (coheratorToStagePushforward S Ksys stageIso Klim P n) ≫
    Hom.DerivedBaseChange.app
      (IsPullback.of_hasPullback f (p n)).flip.toCommSq (S.K n)

/-- The affine direct-image comparison identifies global sections of a derived
pushforward with scalar restriction of global sections on the stage fibre product. -/
noncomputable def etalePushforwardGlobalSectionsLeray
    (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (f : U ⟶ X) (n : ℕ) (G : ModuleDerived (Limits.pullback f (p n))) :
    (limitGlobalSections U).obj
        ((Modules.moduleDerivedPushforward (Limits.pullback.fst f (p n))).obj G) ⟶
      (ModuleCat.derivedRestrictionOfScalars (A_lim.cone.stageMap n).hom).obj
        ((etaleStageGlobalSections p q f n).obj G) :=
  (Modules.AffineGlobalSections.pushforwardIso
      (φ := A_lim.cone.stageMap n)
      (g' := Limits.pullback.fst f (p n))
      (f := SchemeRealization.toBase U)
      (f' := Limits.pullback.snd f (p n) ≫ q n)
      (w := Category.comp_id _)
      (CommSq.mk ((SchemeRealization.eq_toBase _).trans
        (SchemeRealization.eq_toBase _).symm))).hom.app G

/-- The Leray comparison is the component of the affine direct-image isomorphism
for the stage fibre product and its morphism to the affine stage base. -/
theorem etalePushforwardGlobalSectionsLeray_def
    (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) (f : U ⟶ X) (n : ℕ) (G : ModuleDerived (Limits.pullback f (p n))) :
    etalePushforwardGlobalSectionsLeray p q f n G =
    (Modules.AffineGlobalSections.pushforwardIso
      (φ := A_lim.cone.stageMap n)
      (g' := Limits.pullback.fst f (p n))
      (f := SchemeRealization.toBase U)
      (f' := Limits.pullback.snd f (p n) ≫ q n)
      (w := Category.comp_id _)
      (CommSq.mk ((SchemeRealization.eq_toBase _).trans
        (SchemeRealization.eq_toBase _).symm))).hom.app G :=
  rfl

/-- The restriction-side comparison in `D(A)` induced by `etaleCoheratorToStage`,
followed by the Leray reassociation to the restriction of `RΓ(U_n, K_n)`. -/
noncomputable def etaleGlobalSectionsRestrictionMap
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ) :
    etaleGlobalSections Klim f ⟶
      (ModuleCat.derivedRestrictionOfScalars (A_lim.cone.stageMap n).hom).obj
        ((etaleStageGlobalSections p q f n).obj
          ((modulePullbackDerived (Limits.pullback.snd f (p n))).obj (S.K n))) :=
  (limitGlobalSections U).map
      (etaleCoheratorToStage S Ksys stageIso Klim P f n) ≫
    etalePushforwardGlobalSectionsLeray p q f n
      ((modulePullbackDerived (Limits.pullback.snd f (p n))).obj (S.K n))

/-- `etaleGlobalSectionsRestrictionMap` is derived global sections of
`etaleCoheratorToStage`, followed by `etalePushforwardGlobalSectionsLeray`. -/
theorem etaleGlobalSectionsRestrictionMap_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ) :
    etaleGlobalSectionsRestrictionMap S Ksys stageIso Klim P f n =
      (limitGlobalSections U).map
          (etaleCoheratorToStage S Ksys stageIso Klim P f n) ≫
        etalePushforwardGlobalSectionsLeray p q f n
          ((modulePullbackDerived (Limits.pullback.snd f (p n))).obj (S.K n)) :=
  rfl

/-- The canonical comparison `RΓ(U, K) ⊗ᴸ_A A_n ⟶ RΓ(U_n, K_n)` in `D(A_n)`,
obtained by transposing `etaleGlobalSectionsRestrictionMap`. -/
noncomputable def etaleGlobalSectionsBaseChangeMap
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    Ext.obj (etaleGlobalSections Klim f) ⟶
      (etaleStageGlobalSections p q f n).obj
        ((modulePullbackDerived (Limits.pullback.snd f (p n))).obj (S.K n)) :=
  Ext.transpose
    (etaleGlobalSectionsRestrictionMap S Ksys stageIso Klim P f n)

/-- `etaleGlobalSectionsBaseChangeMap` is the derived-extension transpose of
`etaleGlobalSectionsRestrictionMap`. -/
theorem etaleGlobalSectionsBaseChangeMap_def
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (f : U ⟶ X) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    etaleGlobalSectionsBaseChangeMap S Ksys stageIso Klim P f n Ext =
      Ext.transpose
        (etaleGlobalSectionsRestrictionMap S Ksys stageIso Klim P f n) :=
  rfl

/-- For a compatible pseudo-coherent formal system on a proper, flat, finitely
presented algebraic space, scalar base change of derived global sections on every
étale quasi-compact quasi-separated algebraic space is identified with derived
global sections of the corresponding stage restriction. -/
theorem etaleGlobalSectionsBaseChangeMap_isIso
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    {U : AlgebraicSpace (Spec A_lim.cone.pt)} (f : U ⟶ X)
    [Etale f] [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U] (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    IsIso (etaleGlobalSectionsBaseChangeMap S Ksys stageIso Klim P f n Ext) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
