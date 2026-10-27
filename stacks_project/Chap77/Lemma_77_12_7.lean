/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.ProperSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

universe u

/- Lemma 77.12.7: in Situation 77.12.1, with `K` as in Lemma 77.12.2 and
`W ⊂ X` as in Lemma 77.12.6, after possibly shrinking the open `W`, the
support of `ℱ = H^0(K)|_W` is proper over `A`. -/
@[stacks 0CXA] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.existsOpen_coheratorLimit_hasProperSupport :
    ∀ (S : ProperFlatFormalSystem.{u})
      [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
      (F : SequentialInverseSystem (QCoh S.space))
      (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
        S.pushforwardModule n)
      (Klim : ModuleDerived S.space)
      (P : HomotopyLimit.Presentation
        (F ⋙ QCoh.inclusion S.space ⋙
          DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
      (W : OpenSubspace S.space)
      (hW : IsConcentratedFinitePresentationOpen S F stageIso Klim P W),
      ∃ W' : OpenSubspace S.space,
        W'.pointsSet ⊆ W.pointsSet ∧
          IsConcentratedFinitePresentationOpen S F stageIso Klim P W' ∧
            HasProperSupportOver (W'.ι ≫ SchemeRealization.toBase S.space)
              (restrictDegreeZero S F Klim W'))
