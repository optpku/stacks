module

public import stacks_project.Chap77.Lemma_77_12_5_Comparison
public import stacks_project.Chap77.Lemma_77_12_5_Pullback

/-!
# Lemma 77.12.5

In Situation 77.12.1, with `K` as in Lemma 77.12.2, derived global sections of an
étale quasi-compact quasi-separated open `U ⟶ X` base-change along `A → A_n` to
derived global sections of `ℱ n` on `U_n = U ×_X X_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
open CategoryTheory.DerivedCategory
open Opposite

noncomputable section

universe u

/-- Lemma 77.12.5: in Situation 77.12.1, with `K` as in Lemma 77.12.2, for every
étale morphism `f : U ⟶ X` with `U` quasi-compact and quasi-separated there is a
canonical isomorphism `RΓ(U, K) ⊗ᴸ_A A_n = RΓ(U_n, ℱ n)` in `D(A_n)`, realized as
invertibility of `etaleGlobalSectionsBaseChangeMap`. Here `U_n` is the fibre
product `U ×_X X_n`. -/
@[stacks 0CX8]
theorem etaleGlobalSectionsBaseChangeMap_isIso (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushedStageSuccessor S n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space)
    [Etale f] [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U] (n : ℕ)
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.fst f (S.stageToSpace n)) f)]
    [IsIso (modulePullbackDerived.compComparison
      (Limits.pullback.snd f (S.stageToSpace n)) (S.stageToSpace n))]
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom) :
    IsIso (etaleGlobalSectionsBaseChangeMap S F stageIso Klim P f n Ext) :=
  sorry

