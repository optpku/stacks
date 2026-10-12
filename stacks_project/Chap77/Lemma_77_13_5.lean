/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Lemma_77_13_5_Comparison

/-!
# Lemma 77.13.5

In Situation 77.13.1, with `K` as in Lemma 77.13.2, derived global sections
of an étale quasi-compact quasi-separated open `U ⟶ X` base-change along
`A → A_n` to derived global sections of `K_n` on `U_n = U ×_X X_n`.
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
variable [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]

/-- Lemma 77.13.5: in Situation 77.13.1, with `K` as in Lemma 77.13.2, for every
étale morphism `f : U ⟶ X` with `U` quasi-compact and quasi-separated there is a
canonical isomorphism `RΓ(U, K) ⊗ᴸ_A A_n = RΓ(U_n, K_n)` in `D(A_n)`, realized as
invertibility of `etaleGlobalSectionsBaseChangeMap`. Here `U_n` is the fibre
product `U ×_X X_n`. -/
@[stacks 0DIP]
theorem etaleGlobalSectionsBaseChangeMap_isIso
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [∀ n, IsIso (modulePullbackDerived.compComparison (i n) (p (n + 1)))]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.pushforwardDerived (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    {U : AlgebraicSpace (Spec A_lim.cone.pt)} (f : U ⟶ X)
    [Etale f] [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U] (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.fst f (p n)) f)]
    [IsIso (modulePullbackDerived.compComparison (Limits.pullback.snd f (p n)) (p n))]
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    IsIso (etaleGlobalSectionsBaseChangeMap p q S Ksys stageIso Klim P f n Ext) :=
  sorry
