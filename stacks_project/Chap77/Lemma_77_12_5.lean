/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Etale
import StacksCheckRecall

/-!
# Lemma 77.12.5

In Situation 77.12.1, with `K` as in Lemma 77.12.2, derived global sections of an
étale morphism `U ⟶ X` with `U` quasi-compact and quasi-separated base-change along `A → A_n` to
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

/- Lemma 77.12.5: derived global sections along an étale morphism with
quasi-compact quasi-separated source commute with finite-stage scalar extension. -/
@[stacks 0CX8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.etaleGlobalSectionsBaseChangeMap_isIso :
    ∀ (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardStep S n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    {U : AlgebraicSpace (Spec S.limitCone.cone.pt)} (f : U ⟶ S.space)
    [Etale f] [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U] (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom),
    IsIso (etaleGlobalSectionsBaseChangeMap S F stageIso Klim P f n Ext))
