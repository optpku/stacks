/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation.Substack

/-!
# Substacks of a presentation

Atlas pullback identifies locally closed, closed, and open substacks with
invariant subspaces and detects factorization through each substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 100.9.11 (1): Atlas pullback is a bijection between locally closed
substacks and invariant locally closed subspaces. -/
@[stacks 0507] #check
  (AlgebraicGeometry.AlgebraicStack.Presentation.pullbackLocallyClosed_bijective :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (P : AlgebraicGeometry.AlgebraicStack.Presentation X),
      Function.Bijective P.pullbackLocallyClosed)

/- Lemma 100.9.11 (2): Factorization through a locally closed substack is
detected by atlas pullback. -/
@[stacks 0507] #check
  (AlgebraicGeometry.AlgebraicStack.Presentation.factorsThrough_iff :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {Y : GroupoidsOver S} [AlgebraicStack Y]
      (P : AlgebraicGeometry.AlgebraicStack.Presentation X)
      (Q : AlgebraicGeometry.AlgebraicStack.Substack.LocallyClosed X) (f : Y ⟶ X),
      AlgebraicGeometry.AlgebraicStack.Substack.FactorsThrough f Q.val ↔
        AlgebraicGeometry.AlgebraicStack.Substack.FactorsThrough
          (P.objectProjection f) (P.pullbackLocallyClosed Q).val)

/- Lemma 100.9.11 (3): Atlas pullback is a bijection between closed
substacks and invariant closed subspaces. -/
@[stacks 0507] #check
  (AlgebraicGeometry.AlgebraicStack.Presentation.pullbackClosed_bijective :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (P : AlgebraicGeometry.AlgebraicStack.Presentation X),
      Function.Bijective P.pullbackClosed)

/- Lemma 100.9.11 (4): Factorization through a closed substack is
detected by atlas pullback. -/
@[stacks 0507] #check
  (AlgebraicGeometry.AlgebraicStack.Presentation.closed_factorsThrough_iff :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {Y : GroupoidsOver S} [AlgebraicStack Y]
      (P : AlgebraicGeometry.AlgebraicStack.Presentation X)
      (Q : AlgebraicGeometry.AlgebraicStack.Substack.Closed X) (f : Y ⟶ X),
      AlgebraicGeometry.AlgebraicStack.Substack.FactorsThrough f Q.val ↔
        AlgebraicGeometry.AlgebraicStack.Substack.FactorsThrough
          (P.objectProjection f) (P.pullbackClosed Q).val)

/- Lemma 100.9.11 (5): Atlas pullback is a bijection between open
substacks and invariant open subspaces. -/
@[stacks 0507] #check
  (AlgebraicGeometry.AlgebraicStack.Presentation.pullbackOpen_bijective :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (P : AlgebraicGeometry.AlgebraicStack.Presentation X),
      Function.Bijective P.pullbackOpen)

/- Lemma 100.9.11 (6): Factorization through an open substack is
detected by atlas pullback. -/
@[stacks 0507] #check
  (AlgebraicGeometry.AlgebraicStack.Presentation.open_factorsThrough_iff :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {Y : GroupoidsOver S} [AlgebraicStack Y]
      (P : AlgebraicGeometry.AlgebraicStack.Presentation X)
      (Q : AlgebraicGeometry.AlgebraicStack.Substack.Open X) (f : Y ⟶ X),
      AlgebraicGeometry.AlgebraicStack.Substack.FactorsThrough f Q.val ↔
        AlgebraicGeometry.AlgebraicStack.Substack.FactorsThrough
          (P.objectProjection f) (P.pullbackOpen Q).val)

