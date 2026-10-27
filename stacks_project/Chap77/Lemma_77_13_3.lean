/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Cohomology
import StacksCheckRecall

/-! # Lemma 77.13.3

Tensoring the formal-completion complex with a perfect object gives pseudo-coherent
global sections whose canonical derived base change recovers every finite stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open FormalCompletion FormalCompletion.System
open CategoryTheory.DerivedCategory

noncomputable section

universe u

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]

/- Lemma 77.13.3 (1): pseudo-coherence of tensor global sections. -/
@[stacks 0DIM] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.globalSectionsTensor_isPseudoCoherent :
  ∀ [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n)),
    (∀ n, Ksys.stepMap n ≫ (stageIso n).hom =
      (stageIso (n + 1)).hom ≫ S.pushforwardTransition n) →
    ∀ (Klim : ModuleDerived X), HomotopyLimit.IsOf Ksys Klim →
      ∀ (E : ModuleDerived X), ModuleDerived.IsPerfect E →
        DerivedCategory.IsPseudoCoherent (globalSectionsTensor Klim E))

/- Lemma 77.13.3 (2): canonical derived base change of tensor global sections. -/
@[stacks 0DIM] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.globalSectionsTensorBaseChangeMap_isIso :
  ∀ [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n)),
    (∀ n, Ksys.stepMap n ≫ (stageIso n).hom =
      (stageIso (n + 1)).hom ≫ S.pushforwardTransition n) →
    ∀ (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
      (E : ModuleDerived X), ModuleDerived.IsPerfect E →
      ∀ (n : ℕ) (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom),
        IsIso (globalSectionsTensorBaseChangeMap S Ksys stageIso Klim P E n Ext))
