/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Representable
import StacksCheckRecall

/-!
# Representability of locally quasi-finite separated morphisms

A locally quasi-finite and separated morphism of algebraic spaces over a
scheme is representable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.51.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally quasi-finite and separated, then
`f` is representable. -/
@[stacks 0418] #check
  (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_of_locallyQuasiFinite_separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [LocallyOfFiniteType f] → [LocallyQuasiFinite f] → [Separated f] →
        yoneda.relativelyRepresentable f)

end AlgebraicGeometry.AlgebraicSpace
