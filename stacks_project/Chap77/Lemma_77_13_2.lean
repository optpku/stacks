/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Boundedness
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion

noncomputable section

universe u

/- Lemma 77.13.2: in Situation 77.13.1, the object
K = Rlim in D_QCoh(𝒪_X) of the stages K_n, equivalently
((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj for an ambient
homotopy limit Klim of the pushforwards of K_n in D(𝒪_X), is
DerivedCategory.IsBoundedAbove, i.e. lies in D⁻_QCoh(𝒪_X). -/
@[stacks 0DIL] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.coheratorHomotopyLimit_isBoundedAbove :
    ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
      {X : AlgebraicSpace (Spec A_lim.cone.pt)}
      {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
      {p : ∀ n, Xn n ⟶ X} {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
      {i : ∀ n, Xn n ⟶ Xn (n + 1)}
      [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]
      (S : System A A_lim X Xn p q i)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (Ksys : SequentialInverseSystem (ModuleDerived X))
      (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
        (Modules.moduleDerivedPushforward (p n)).obj (S.K n)),
      (∀ n, Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n) →
      ∀ (Klim : ModuleDerived X), HomotopyLimit.IsOf Ksys Klim →
        DerivedCategory.IsBoundedAbove
          ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj)
