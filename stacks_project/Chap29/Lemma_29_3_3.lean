/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.Reduced
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/-
Lemma 29.3.3: an immersion from a reduced scheme factors as an open immersion followed by a
closed immersion.
-/
@[stacks 03DQ] #check
  (AlgebraicGeometry.Scheme.Hom.exists_openImmersion_closedImmersion_factorization_of_isReduced :
    ∀ {X Z : Scheme.{u}} (h : Z ⟶ X) [IsImmersion h] [IsReduced Z],
      ∃ (Zbar : Scheme.{u}) (j : Z ⟶ Zbar) (i : Zbar ⟶ X),
        IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = h)
