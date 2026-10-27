/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.FormalExistence
import StacksCheckRecall

/-! # Approximation of coherent sheaves is an equivalence

For a separated morphism of finite presentation over a locally Noetherian scheme,
maximal-adic restriction of coherent-sheaf objects is an equivalence.

As authorized in source-issues/registry.json, key 07X6, the source category keeps
the same objects over Noetherian complete local `S`-algebras with finite-type
residue fields, but its morphisms must induce local `S`-algebra homomorphisms.
This corrects the full-subcategory assertion in Equation 98.9.3.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 99.5.10: in Situation 99.5.1, if `S` is locally Noetherian and
`f : X ⟶ B` is separated, the approximation functor for coherent sheaves is
an equivalence. -/
@[stacks 08W9] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.instApproximationIsEquivalence :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      {X B : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ B),
      [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f] →
      [AlgebraicGeometry.AlgebraicSpace.Separated f] →
      (AlgebraicGeometry.GroupoidsOver.approximation
        (AlgebraicGeometry.AlgebraicSpace.CohStack.toGroupoids f)).IsEquivalence)
