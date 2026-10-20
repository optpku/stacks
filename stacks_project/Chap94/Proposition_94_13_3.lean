/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Setoids
import StacksCheckRecall

/-!
# Algebraic stacks with no automorphisms

For an algebraic stack over a scheme `S`, being a stack in setoids, the
canonical inertia 1-morphism being an equivalence, and being representable by
an algebraic space are equivalent. Unlike Lemma 94.13.2, Deligne–Mumford is
not assumed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Proposition 94.13.3 (1): let `S` be a scheme contained in `Sch_fppf`. Let
`X` be an algebraic stack over `S`. Then `X` is a stack in setoids if and only
if the canonical 1-morphism `Inertia.forget X : inertia X ⟶ X` is an
equivalence. -/
@[stacks 04SZ]
#check (AlgebraicGeometry.AlgebraicStack.inSetoids_iff_inertia_isEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ↔
      (toBasedFunctor (forget.{u + 1, u, u, u + 1} X)).IsEquivalence)

/- Proposition 94.13.3 (2): let `S` be a scheme contained in `Sch_fppf`. Let
`X` be an algebraic stack over `S`. Then `X` is a stack in setoids if and only
if `X` is representable by an algebraic space. -/
@[stacks 04SZ]
#check (AlgebraicGeometry.AlgebraicStack.isRepresentableByAlgebraicSpace_iff_inSetoids :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ↔
      IsRepresentableByAlgebraicSpace X)

/- Proposition 94.13.3 (3): let `S` be a scheme contained in `Sch_fppf`. Let
`X` be an algebraic stack over `S`. Then the canonical 1-morphism
`Inertia.forget X : inertia X ⟶ X` is an equivalence if and only if `X` is
representable by an algebraic space. -/
@[stacks 04SZ]
#check (AlgebraicGeometry.AlgebraicStack.isRepresentableByAlgebraicSpace_iff_inertia_isEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (toBasedFunctor (forget.{u + 1, u, u, u + 1} X)).IsEquivalence ↔
      IsRepresentableByAlgebraicSpace X)

end AlgebraicGeometry.AlgebraicStack
