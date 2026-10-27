/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.PseudoCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion

noncomputable section

universe u

/- Lemma 77.13.4: in Situation 77.13.1, the object
K as in Lemma 77.13.2, equivalently
((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj for an ambient
homotopy limit Klim of the pushforwards of K_n in D(𝒪_X), is
pseudo-coherent on X. -/
@[stacks 0DIN] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.coheratorHomotopyLimit_isPseudoCoherent :
    ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
      {X : AlgebraicSpace (Spec A_lim.cone.pt)}
      {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
      {p : ∀ n, Xn n ⟶ X} {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
      {i : ∀ n, Xn n ⟶ Xn (n + 1)}
      [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
      [FinitePresentation (SchemeRealization.toBase X)]
      (S : System A A_lim X Xn p q i)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (Ksys : SequentialInverseSystem (ModuleDerived X))
      (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
        (Modules.moduleDerivedPushforward (p n)).obj (S.K n)),
      (∀ n, Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n) →
      ∀ (Klim : ModuleDerived X), HomotopyLimit.IsOf Ksys Klim →
        IsPseudoCoherent X
          ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj)
