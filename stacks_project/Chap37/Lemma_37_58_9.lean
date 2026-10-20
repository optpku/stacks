/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.Products
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 37.58.9: for a locally finite type morphism, relative finite presentation of the
binary biproduct of two quasicoherent modules implies relative finite presentation of both
summands. -/
@[stacks 09TE] #check
  (AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver.summands_of_biprod :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (F F' : X.Modules) [F.IsQuasicoherent] [F'.IsQuasicoherent],
      (F ⊞ F').IsFinitePresentationOver f →
        F.IsFinitePresentationOver f ∧ F'.IsFinitePresentationOver f)
