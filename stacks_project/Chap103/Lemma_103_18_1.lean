/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.FilteredColimit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack
open GroupoidsOver

universe u

/- Lemma 103.18.1: let `X` be a Noetherian algebraic stack.
Every quasi-coherent `𝒪_X`-module is the filtered colimit of its coherent submodules. -/
@[stacks 0GRF] #check
  (AlgebraicGeometry.AlgebraicStack.coherentSubobjects_isFilteredColimit :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsNoetherian X]
      (F : SheafOfModules.{u} (structureSheaf X)) [F.IsQuasicoherent],
      CategoryTheory.IsFiltered (coherentSubobjects F) ∧
        Nonempty (CategoryTheory.Limits.IsColimit (coherentSubobjectsCocone F)))
