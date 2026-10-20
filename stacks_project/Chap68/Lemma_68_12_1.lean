/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Specialization

/-!
# No specializations in étale fibres over a decent algebraic space

An étale morphism from a scheme to a decent algebraic space has no nontrivial
specializations among scheme points that map to the same point of the algebraic
space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.12.1: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `φ : ofOver U ⟶ X` be an étale morphism from a scheme to `X`. If `u, u' : U.left`
map to the same point of `Points X`, and `u' ⤳ u`, then `u = u'`. -/
@[stacks 03K5] #check
  (AlgebraicGeometry.AlgebraicSpace.eq_of_specializes_of_isDecent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {U : Over S}
      (φ : ofOver U ⟶ X) [Etale φ] {u u' : U.left},
      Points.mapOfOver φ u = Points.mapOfOver φ u' → Specializes u' u → u = u')

end AlgebraicGeometry.AlgebraicSpace
