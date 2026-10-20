/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ProEtale.Cofiltered
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

/- Lemma 61.18.2: for a scheme `S` and a geometric point `s` of `S`, the category of pro-étale
neighbourhoods of `s` is cofiltered. -/
@[stacks 0F6B] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.ProetaleNeighborhood.instIsCofiltered :
    ∀ {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
      (point : Spec (.of K) ⟶ S),
      IsCofiltered ((Scheme.ProEt.forget S ⋙ coyoneda.obj (op (Over.mk point))).Elements))
