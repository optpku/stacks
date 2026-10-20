/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 27.16.10: relative `Proj` and its graded twist algebra commute with arbitrary base
change of schemes. -/
@[stacks 01O3] #check
  (AlgebraicGeometry.Scheme.Hom.relativeProjBaseChangeExists :
    ∀ {S S' X : Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p)
      (sourceTwistAlgebra :
        AlgebraicGeometry.Scheme.Hom.RelativeProjTwistAlgebra P)
      (g : S' ⟶ S),
      ∃ baseChange : AlgebraicGeometry.Scheme.Hom.RelativeProjBaseChange P g,
        baseChange.sourceTwistAlgebra = sourceTwistAlgebra)
