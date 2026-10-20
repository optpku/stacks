/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Specialization

/-!
# No specializations in étale fibres with finite étale covering

An étale morphism from a scheme to an algebraic space has no nontrivial
specializations among scheme points that map to the same point, whenever that
point satisfies the equivalent finite-fibre conditions of Lemma 68.4.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.7.1: Specializing points of an étale scheme chart above a point
admitting an étale scheme covering with finite fibres are equal. -/
@[stacks 03IM] #check
  (AlgebraicGeometry.AlgebraicSpace.eq_of_specializes_of_existsEtaleCoverFiniteFibre :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
      (φ : ofOver U ⟶ X) [Etale φ] {u u' : U.left} {x : Points X},
      Points.mapOfOver φ u = x → Points.mapOfOver φ u' = x →
      Specializes u' u → existsEtaleCoverFiniteFibre X x → u = u')

#check
  (AlgebraicGeometry.AlgebraicSpace.eq_of_specializes_of_forallAffineEtaleFiniteFibre :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
      (φ : ofOver U ⟶ X) [Etale φ] {u u' : U.left} {x : Points X},
      Points.mapOfOver φ u = x → Points.mapOfOver φ u' = x →
      Specializes u' u → forallAffineEtaleFiniteFibre X x → u = u')

end AlgebraicGeometry.AlgebraicSpace
