/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap77.Lemma_77_13_2_Boundedness

/-!
# Pseudo-coherence of the coherator of a formal-completion homotopy limit

The quasi-coherent coreflection of an ambient homotopy limit of the
pushforwards of a Situation 77.13.1 system is pseudo-coherent on `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

section

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]

/-- The quasi-coherent coreflection of an ambient homotopy limit of the
pushforwards of a formal-completion system is pseudo-coherent on the
ambient algebraic space. -/
theorem coheratorHomotopyLimit_isPseudoCoherent (S : System A A_lim X Xn p q i)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (hKlim : HomotopyLimit.IsOf Ksys Klim) :
    IsPseudoCoherent X ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
