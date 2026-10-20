/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Approximation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 68.6.4: A quasi-compact reasonable algebraic space admits a filtered qcqs
étale-surjective approximation, also on sections over quasi-compact schemes, with a
local-isomorphism approximation by schemes when the target is a scheme. -/
@[stacks 03K0] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_qcqs_etale_approximation :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [AlgebraicSpace.IsQuasiCompact X] [AlgebraicSpace.IsReasonable X],
      ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
        (F : J ⥤ AlgebraicSpace S) (ι : F ⟶ (Functor.const J).obj X),
        AlgebraicSpace.IsQCQSEtaleApproximation F ι ∧
          (AlgebraicSpace.IsScheme X → AlgebraicSpace.IsQCQSLocalIsoApproximation F ι))

#check (AlgebraicGeometry.AlgebraicSpace.exists_qcqs_localIso_approximation :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [AlgebraicSpace.IsQuasiCompact X] [AlgebraicSpace.IsReasonable X]
    [AlgebraicSpace.IsScheme X],
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (F : J ⥤ AlgebraicSpace S) (ι : F ⟶ (Functor.const J).obj X),
      AlgebraicSpace.IsQCQSEtaleApproximation F ι ∧
        AlgebraicSpace.IsQCQSLocalIsoApproximation F ι)
