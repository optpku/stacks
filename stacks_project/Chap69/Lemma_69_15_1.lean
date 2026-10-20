/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.FilteredColimit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.15.1: let `S` be a scheme. Let `X` be a Noetherian algebraic space over `S`.
Every quasi-coherent `𝒪_X`-module is the filtered colimit of its coherent submodules. -/
@[stacks 07UV] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.coherentSubobjects_isFilteredColimit :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (F : X.Modules) [F.IsQuasicoherent],
      CategoryTheory.IsFiltered
          (AlgebraicGeometry.AlgebraicSpace.Modules.coherentSubobjects F) ∧
        Nonempty (CategoryTheory.Limits.IsColimit
          (AlgebraicGeometry.AlgebraicSpace.Modules.coherentSubobjectsCocone F)))
