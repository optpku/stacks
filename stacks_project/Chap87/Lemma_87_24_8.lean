/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.Noetherian
import StacksCheckRecall

/-!
# Locally of finite type over locally Noetherian formal algebraic spaces

A morphism of formal algebraic spaces that is locally of finite type into a
locally Noetherian target has locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.24.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. If `Y` is locally Noetherian and `f` is
locally of finite type, then `X` is locally Noetherian. -/
@[stacks 0AQ7] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.isLocallyNoetherian :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y], IsLocallyNoetherian X)
