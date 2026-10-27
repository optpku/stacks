/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Stratification
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.GerbeStratification

/- Lemma 101.29.3 (1): a stack with quasi-compact inertia admits a well-ordered
stratification by reduced locally closed gerbes dense in their closed remainders. -/
@[stacks 06RF] #check (AlgebraicGeometry.AlgebraicStack.GerbeStratification.exists_dense :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)],
    ∃ (I : Type (u + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (U : I → Substack.LocallyClosed X),
      IsStratification U ∧ (∀ i, remainder U i ⊆ closure (U i).pointsSet))

/- Lemma 101.29.3 (2): the strata can instead all be chosen quasi-compact. -/
@[stacks 06RF] #check (AlgebraicGeometry.AlgebraicStack.GerbeStratification.exists_quasiCompact :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)],
    ∃ (I : Type (u + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (U : I → Substack.LocallyClosed X),
      IsStratification U ∧ (∀ i, IsQuasiCompact (U i).category))

/- Lemma 101.29.3 (3): the dense strata can be chosen as the largest open gerbes
in the reduced closed substacks on the successive remainders. -/
@[stacks 06RF] #check (AlgebraicGeometry.AlgebraicStack.GerbeStratification.exists_maximal_dense :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)],
    ∃ (I : Type (u + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I)
      (U : I → Substack.LocallyClosed X), IsMaximalDense U)

/- Lemma 101.29.3 (4): maximal dense stratifications are canonical up to order
isomorphism of the indices and equality of the substack object properties. -/
@[stacks 06RF] #check (AlgebraicGeometry.AlgebraicStack.GerbeStratification.unique_maximal_dense :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    {I J : Type (u + 1)}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder J] [WellFoundedLT J]
    (U : I → Substack.LocallyClosed X) (V : J → Substack.LocallyClosed X),
    IsMaximalDense U → IsMaximalDense V →
      ∃ e : I ≃o J, ∀ i, (U i).val = (V (e i)).val)

end AlgebraicGeometry.AlgebraicStack.GerbeStratification
