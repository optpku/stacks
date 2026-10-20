/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Positivity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.45.9: Let `k` be a field, let `X` be proper over `k`, let `Z ⊆ X` be a closed
subscheme of dimension `d`, and let `L : Fin d → X.Modules` be a family of ample invertible
modules. Then the intersection number of the family with `Z` is strictly positive. -/
@[stacks 0BEV] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.number_pos_of_isAmple :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ}
      (hZdim : topologicalKrullDim Z.subscheme = d)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : Fin d → X.Modules)
      [∀ j : Fin d, AlgebraicGeometry.Scheme.Modules.Invertible (L j)]
      [∀ j : Fin d, AlgebraicGeometry.Scheme.Modules.IsAmple (L j)],
      0 < AlgebraicGeometry.Scheme.Modules.Intersection.number k f Z hZdim L)
