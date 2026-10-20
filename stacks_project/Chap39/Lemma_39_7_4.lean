/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.GroupScheme.Stalk

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

/- Lemma 39.7.4 (1): Every local ring of a group scheme over a field has a unique
minimal prime ideal. -/
@[stacks 047M] #check
  (AlgebraicGeometry.GroupScheme.existsUniqueMinimalPrime_stalk :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] (g : G.left),
      ∃! p : Ideal (SchemeOverField.stalkRing G g),
        p ∈ minimalPrimes (SchemeOverField.stalkRing G g))

/- Lemma 39.7.4 (2): Exactly one irreducible component of a group scheme over a field
contains its identity point. -/
@[stacks 047M] #check
  (AlgebraicGeometry.GroupScheme.existsUniqueIrreducibleComponent_throughIdentity :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G],
      ∃! Z : irreducibleComponents G.left,
        η[G].left (IsLocalRing.closedPoint k) ∈ (Z : Set G.left))

/- Lemma 39.7.4 (3): An irreducible component of a group scheme over a field that contains
the identity point is geometrically irreducible over the field. -/
@[stacks 047M] #check
  (AlgebraicGeometry.GroupScheme.geometricallyIrreducible_identityComponent :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G]
      (Z : irreducibleComponents G.left),
      η[G].left (IsLocalRing.closedPoint k) ∈ (Z : Set G.left) →
        GeometricallyIrreducible
          (G.left.irreducibleComponentSubschemeι Z ≫ G.hom))
