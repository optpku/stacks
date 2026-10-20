/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Limits
import StacksCheckRecall

/-!
# Fibre products and equalizers of groupoid fibrations

A category fibred in groupoids over `(Sch/S)_fppf` has fibre products. If its
Isom-presheaves are algebraic spaces, it has equalizers. Algebraic stacks, and
more generally quotient stacks, have equalizers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 96.17.2 (1): a category fibred in groupoids over `(Sch/S)_fppf`
has fibre products in its total category. -/
@[stacks 06WY] #check (AlgebraicGeometry.GroupoidsOver.hasPullbacks :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), HasPullbacks X.total)

/- Lemma 96.17.2 (2): algebraic-space Isom-presheaves imply equalizers. -/
@[stacks 06WY] #check (AlgebraicGeometry.GroupoidsOver.hasEqualizers_of_isomorphismPresheaf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    isomorphismPresheaf.isAlgebraicSpace X → HasEqualizers X.total)

/- Lemma 96.17.2 (3): quotient stacks have equalizers. -/
@[stacks 06WY] #check (AlgebraicGeometry.GroupoidsOver.hasEqualizers_quotientStack :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
    HasEqualizers (GroupoidAlgebraicSpace.SmallQuotient.quotientStack G).total)

/- Lemma 96.17.2 (3): algebraic stacks have equalizers. -/
@[stacks 06WY] #check (AlgebraicGeometry.GroupoidsOver.hasEqualizers :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    HasEqualizers X.total)
