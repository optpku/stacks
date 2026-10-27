/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DMLocus.Open
import StacksCheckRecall

/-!
# Largest open DM and quasi-DM substacks

An algebraic stack has a largest open DM substack and a largest open quasi-DM
substack, nested as open substacks of the ambient stack.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.22.1 (1): Let `X` be an algebraic stack. There is a largest open
DM substack of `X`. -/
@[stacks 0DSM] #check (AlgebraicGeometry.AlgebraicStack.dmLocus_spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsDM (Substack.Open.category (dmLocus X)) ∧
      ∀ V : Substack.Open X, IsDM (Substack.Open.category V) →
        V.pointsSet ⊆ (dmLocus X).pointsSet)

/- Lemma 101.22.1 (2): Let `X` be an algebraic stack. There is a largest open
quasi-DM substack of `X`. -/
@[stacks 0DSM] #check (AlgebraicGeometry.AlgebraicStack.quasiDMLocus_spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsQuasiDM (Substack.Open.category (quasiDMLocus X)) ∧
      ∀ V : Substack.Open X, IsQuasiDM (Substack.Open.category V) →
        V.pointsSet ⊆ (quasiDMLocus X).pointsSet)

/- Lemma 101.22.1 (3): Let `X` be an algebraic stack. The largest open DM
substack of `X` is contained in the largest open quasi-DM substack. -/
@[stacks 0DSM] #check (AlgebraicGeometry.AlgebraicStack.dmLocus_subset_quasiDMLocus :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (dmLocus X).pointsSet ⊆ (quasiDMLocus X).pointsSet)

end AlgebraicGeometry.AlgebraicStack
