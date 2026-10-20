/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.15.8: let `f : X ⟶ Y` be a morphism of schemes over a base scheme `S`, exhibited by
`g : Y ⟶ S`. If `X` is locally of finite type over `S`, i.e. if the composite `f ≫ g : X ⟶ S` is
locally of finite type, then `f` is locally of finite type. -/
@[stacks 01T8] #check
  (AlgebraicGeometry.locallyOfFiniteType_of_comp :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType (f ≫ g)],
      LocallyOfFiniteType f)
