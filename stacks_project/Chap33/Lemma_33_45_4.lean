/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.45.4: in the situation of Definition 33.45.3, the intersection number
`(L_1 ⋯ L_d · Z)` is an integer. -/
@[stacks 0BEQ] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.number_isInteger :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ}
      (hZdim : topologicalKrullDim Z.subscheme = d)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : Fin d → X.Modules)
      [∀ j : Fin d, AlgebraicGeometry.Scheme.Modules.Invertible (L j)],
      IsLocalization.IsInteger ℤ
        (AlgebraicGeometry.Scheme.Modules.Intersection.number k f Z hZdim L))
