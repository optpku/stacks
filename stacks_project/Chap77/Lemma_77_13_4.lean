/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Lemma_77_13_4_PseudoCoherent
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
  (System.coheratorHomotopyLimit_isPseudoCoherent :
    ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
      {X : AlgebraicSpace (Spec A_lim.cone.pt)}
      {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
      {p : ∀ n, Xn n ⟶ X} {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
      {i : ∀ n, Xn n ⟶ Xn (n + 1)}
      [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]
      (S : System A A_lim X Xn p q i)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
      (Ksys : SequentialInverseSystem (ModuleDerived X))
      (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
        (Modules.pushforwardDerived (p n)).obj (S.K n)),
      (∀ n, Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n) →
      ∀ (Klim : ModuleDerived X), HomotopyLimit.IsOf Ksys Klim →
        IsPseudoCoherent X
          ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj)
