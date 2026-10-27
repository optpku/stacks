/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Concentration
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 77.12.6: in Situation 77.12.1, with `K` as in Lemma 77.12.2, the
closed subset `X_0 ⊂ |X|` of points lying over `Spec(A_n) ⊂ Spec(A)` is
contained in an open subspace `W ⊂ X` on which `H^i(K)|_W` vanishes for
`i ≠ 0`, the sheaf `ℱ = H^0(K)|_W` is of finite presentation, and
`ℱ n = ℱ ⊗_{𝒪_X} 𝒪_{X_n}` via the canonical stage comparison. -/
@[stacks 0CX9] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.existsOpen_coheratorLimit_concentrated_finitePresentation :
    ∀ (S : ProperFlatFormalSystem.{u})
      [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
      (F : SequentialInverseSystem (QCoh S.space))
      (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
        S.pushforwardModule n)
      (stageIso_naturality : ∀ n,
        (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
          (stageIso (n + 1)).hom ≫ ProperFlatFormalSystem.pushforwardStep S n)
      (Klim : ModuleDerived S.space)
      (P : HomotopyLimit.Presentation
        (F ⋙ QCoh.inclusion S.space ⋙
          DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim),
      ∃ W : OpenSubspace S.space,
        ProperFlatFormalSystem.IsConcentratedFinitePresentationOpen S F stageIso Klim P W)
