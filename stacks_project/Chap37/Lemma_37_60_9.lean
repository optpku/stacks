/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.60.9: a morphism to a locally Noetherian scheme is pseudo-coherent if and only if
it is locally of finite type. -/
@[stacks 0684] #check
  (AlgebraicGeometry.PseudoCoherent.iff_locallyOfFiniteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsLocallyNoetherian S],
      AlgebraicGeometry.PseudoCoherent f ↔ AlgebraicGeometry.LocallyOfFiniteType f)
