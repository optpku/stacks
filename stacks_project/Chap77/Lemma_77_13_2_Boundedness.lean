/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Boundedness
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_19_1_Instances
public import stacks_project.Chap75.Remark_75_20_6_Counit
public import stacks_project.Chap77.Situation_77_13_1_FormalCompletion
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction

/-!
# Formal-completion boundedness API

The canonical pushforward transitions and boundedness result are available
through their shared mathematical owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.pushforwardTransition :
    ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
      {X : AlgebraicSpace (Spec A_lim.cone.pt)}
      {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
      {p : ∀ n, Xn n ⟶ X} {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
      {i : ∀ n, Xn n ⟶ Xn (n + 1)}
      [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]
      (S : System A A_lim X Xn p q i) (n : ℕ),
    (Modules.moduleDerivedPushforward (p (n + 1))).obj (S.K (n + 1)) ⟶
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.pushforwardTransition_spec :
    ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
      {X : AlgebraicSpace (Spec A_lim.cone.pt)}
      {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
      {p : ∀ n, Xn n ⟶ X} {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
      {i : ∀ n, Xn n ⟶ Xn (n + 1)}
      [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]
      (S : System A A_lim X Xn p q i) (n : ℕ),
    S.pushforwardTransition n =
      (Modules.moduleDerivedPushforward (p (n + 1))).map
          (((Modules.derivedPullbackPushforwardAdjunction (i n)).homEquiv
              (S.K (n + 1)) (S.K n)) (S.transitionIso n).hom) ≫
        (Modules.pushforwardDerived.compIso (i n) (p (n + 1))).hom.app (S.K n) ≫
        eqToHom (congrArg (fun g : Xn n ⟶ X ↦
          (Modules.moduleDerivedPushforward g).obj (S.K n)) (S.comp_p n)))

#check
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
