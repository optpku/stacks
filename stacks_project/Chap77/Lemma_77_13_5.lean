/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Etale

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

/- Lemma 77.13.5: Étale quasi-compact quasi-separated derived global sections
commute with formal-completion scalar base change. -/
@[stacks 0DIP] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.etaleGlobalSectionsBaseChangeMap_isIso :
  ∀ [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
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
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom),
    IsIso (etaleGlobalSectionsBaseChangeMap S Ksys stageIso Klim P f n Ext))
