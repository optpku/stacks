/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.ProperDiscreteFieldFibers

/-!
# Finite morphisms of algebraic spaces over a locally Noetherian target

A morphism of algebraic spaces over a locally Noetherian target is finite if
and only if it is proper and has discrete field fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 69.23.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is locally Noetherian. Then `f` is
finite if and only if `f` is proper and every field fibre is discrete, i.e.
`discreteFieldFibers f`. A more general version without local Noetherianity
is Lemma 76.35.1. -/
@[stacks 0A4V] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.iff_proper_and_discreteFieldFibers_of_isLocallyNoetherian :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
      (f : X ⟶ Y), IsFinite f ↔ Proper f ∧ discreteFieldFibers f)

end AlgebraicGeometry.AlgebraicSpace
