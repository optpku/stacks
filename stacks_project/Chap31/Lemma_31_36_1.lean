/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Modification
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.36.1: Let `X` be an integral scheme and let `E` be a finite locally free
`𝒪_X`-module. There exists a modification `f : X' ⟶ X` such that the pullback of `E` has a
filtration whose successive quotients are invertible `𝒪_{X'}`-modules. -/
@[stacks 0AYP] #check
  (AlgebraicGeometry.Scheme.Modules.exists_modification_with_invertibleQuotientFiltration :
    ∀ (X : Scheme.{u}) [IsIntegral X] (E : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree E],
      ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
        IsModification f ∧
          AlgebraicGeometry.Scheme.Modules.HasInvertibleQuotientFiltration
            ((AlgebraicGeometry.Scheme.Modules.pullback f).obj E))
