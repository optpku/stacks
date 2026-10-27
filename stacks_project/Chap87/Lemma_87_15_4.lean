/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

universe u

/- Lemma 87.15.4: For morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` of formal
algebraic spaces over a scheme `S`, the canonical comparison from the fibre
product of their reductions to their fibre product induces an isomorphism
`reducedPullbackOfReductions f g ≅ reduction (pullback f g)`. -/
@[stacks 0CB9] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.reductionPullback_isIso :
    ∀ {S : Scheme.{u}}
      [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
      [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
      {X Y Z : Sheaf (full.bigTopology S) (Type (u + 1))}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
      (f : X ⟶ Z) (g : Y ⟶ Z),
    IsIso (reductionPullbackMap f g))
